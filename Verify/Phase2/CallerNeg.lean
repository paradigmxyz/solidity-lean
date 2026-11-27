import Verify.Phase2.CounterCaller

/-!
# Negative control: a property that depends on the caller does not certify from every caller

`neg_spec` is `bump`'s spec with the ensures clause `msg.sender == 0x2000`. It holds at the fixed
caller of the one-caller route and fails from every other caller, so:

* `neg_fixed`: the one-caller route's premise holds (`TreeMeetsFixed` at `ctx0` = `ctxAt 0x2000 0`,
  the tree at `callerWord`): a statement fixed to `0x2000` would certify it. That is why the caller must
  be in the statement.
* `neg_tree_not_from`: the every-caller premise of `CallerFrom.property_from` is **false** (caller
  `0x3000`, `bump(0)` from empty storage succeeds); so no instance of the generic theorem exists for it,
  and the generator's `tree_meets_fixed` proof of it fails (tools/certify/test_loop_any_caller.py).
* `neg_not_property_from`: the every-caller property itself is **false** of SolidCore's Counter.
* `neg_property_under_premise`: it certifies only under the explicit premise `x = 0x2000`.
-/

namespace Verify.Phase2.CallerNeg

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec
open SolidCore.Verify.AnyCaller SolidCore.Verify.Generic Verify.LoopSource.Generic Verify.Phase2.CallerFrom
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed idStep)
open Contracts.VerifyCounter.Source (contract? fuel bumpSel)
open Verify.LoopSource.MirLink (bumpCall)
open Verify.Phase2.CounterCaller (T)

/-- `bump`'s spec with the caller-dependent ensures `msg.sender == 0x2000`. -/
def neg_spec : FnSpec :=
  { name := "Counter.bump",
    selector := 0xb20eb4c4,
    params := [(.uint 256)],
    rets := [],
    payable := false,
    requires := [],
    ensures := [(.bin .eq (.env .sender) (.lit 0x2000))],
    succeedsIf := [] }

/-- A bundle with that one function spec. -/
def Bneg : Bundle where
  fuel := 0
  spec := { name := "Counter", fns := [], invariants := [], ghosts := [], specs := [neg_spec] }

/-- **The one-caller route's premise holds**: at `ctx0` with the tree at `callerWord`. -/
theorem neg_fixed : TreeMeetsFixed Bneg neg_spec (ctxAt 0x2000 0) 1 T := by
  tree_meets_fixed [T, Verify.LoopSource.Equiv.CounterObl.T, neg_spec, Bneg, SolidCore.Spec.ctxAt,
    SolidCore.Refinement.Generic.UnOp.eval]

/-- **The every-caller premise is false**: from caller `0x3000`, `bump(0)` from empty storage succeeds
and `msg.sender == 0x2000` fails. -/
theorem neg_tree_not_from :
    ¬ ∀ a, a < 2 ^ 160 → a ≠ selfAddress → TreeMeetsFixedAt a Bneg neg_spec (ctxAt a 0) 1 T := by
  intro h
  have hp := h 0x3000 (by decide) (by decide) [0] (fun _ => 0) [0] ⟨fun _ => 0, Ghost.zero, 1⟩ rfl
    (by simp) (fun _ => by decide) rfl rfl (by simp [ctxAt]) (by simp [Bundle.satAll, Bneg, neg_spec])
    (by simp [Bundle.satAll, Bneg])
  have hs : (T.eval ⟨[0], fun _ => 0, solHash, 0x3000⟩).obs.success = true := by decide +kernel
  obtain ⟨rets, -, hens, -⟩ := hp.1 hs
  simp [Bundle.satAll, Bundle.sat, Bneg, neg_spec, eval, mkEnv, ctxAt, BinOp.apply] at hens

/-- **The every-caller property is false of SolidCore's Counter.** -/
theorem neg_not_property_from :
    ¬ ∀ c, contract? = .ok c → ∀ x : Nat, x < 2 ^ 160 → x ≠ selfAddress →
      ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
      ∀ obs, (Loop.solidCoreRuntimeFrom x fuel).run c (bumpCall σ a) = some obs →
        bundlePost Bneg (ctxOfCallFrom x) idStep (bumpCall σ a) obs := by
  intro h
  obtain ⟨c, hc⟩ := Contracts.VerifyCounter.Source.contract_ok
  have hrun := Verify.Partial.CounterAny.src_run_rt hc 0x3000 (by decide) [] (a := 0) (by decide)
  have hp := h c hc 0x3000 (by decide) (by decide) [] 0 (by decide) _ hrun
  have hpre : Pre Bneg neg_spec (ctxOfCallFrom 0x3000 (bumpCall [] 0)) ⟨slotValue [], Ghost.zero, 1⟩
      (bumpCall [] 0) [0] := by
    refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
    · decide
    · exact SolidCore.Refinement.Shapes.selectorOf_calldata (by decide) [0] 0 []
    · have := SolidCore.Spec.words_calldata bumpSel (args := [0]) (by simp)
      simp only [bumpCall] at this ⊢
      rw [this]; decide
    · simp [ctxOfCallFrom]
    · simp [Bundle.satAll, Bneg, neg_spec]
    · simp [Bundle.satAll, Bneg]
  have hs : (Verify.LoopSource.Equiv.CounterObl.T.eval
      (Verify.LoopSource.Equiv.CounterCtx.ρOf [] 0 0x3000)).obs.success = true := by decide +kernel
  obtain ⟨rets, -, hens, -⟩ := (hp neg_spec (List.mem_singleton_self _) [0] _ hpre).1 hs
  simp [Bundle.satAll, Bundle.sat, Bneg, neg_spec, eval, mkEnv, ctxOfCallFrom, BinOp.apply] at hens

/-- The tree meets `neg_spec` for the caller `0x2000`. -/
theorem neg_at_premise : ∀ a, a = 0x2000 → TreeMeetsFixedAt a Bneg neg_spec (ctxAt a 0) 1 T := by
  rintro a rfl
  tree_meets_fixed [T, Verify.LoopSource.Equiv.CounterObl.T, neg_spec, Bneg, SolidCore.Spec.ctxAt,
    SolidCore.Refinement.Generic.UnOp.eval]

/-- **It certifies only under the explicit premise `x = 0x2000`.** -/
theorem neg_property_under_premise : ∀ c, contract? = .ok c → ∀ x : Nat, x = 0x2000 →
    ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
    ∀ obs, (Loop.solidCoreRuntimeFrom x fuel).run c (bumpCall σ a) = some obs →
      bundlePost Bneg (ctxOfCallFrom x) idStep (bumpCall σ a) obs := by
  intro c hc x hx σ a ha obs hrun
  have hm : ∀ fs ∈ Bneg.spec.specs, fs.selector = bumpSel → TreeMeetsFixedAt x Bneg fs (ctxAt x 0) 1 T := by
    intro fs hfs _
    simp only [Bneg, List.mem_singleton] at hfs
    subst hfs
    exact neg_at_premise x hx
  exact (property_at (by decide) (Contracts.VerifyCounter.Source.shape_of hc).2.2 (ws := [2 ^ 256 - 1]) rfl rfl
    (Verify.LoopSource.Equiv.CounterCtx.bodyRunsFrom hc) Verify.LoopSource.Equiv.CounterCtx.treeFrom
    (by subst hx; decide) hm _ ⟨σ, [a], Verify.LoopSource.MirLink.args_one ha, rfl⟩ obs hrun).1

end Verify.Phase2.CallerNeg

/-- info: 'Verify.Phase2.CallerNeg.neg_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerNeg.neg_fixed

/-- info: 'Verify.Phase2.CallerNeg.neg_tree_not_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerNeg.neg_tree_not_from

/-- info: 'Verify.Phase2.CallerNeg.neg_not_property_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerNeg.neg_not_property_from

/-- info: 'Verify.Phase2.CallerNeg.neg_property_under_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerNeg.neg_property_under_premise
