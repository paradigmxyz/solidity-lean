import Verify.Spec.Tree
import Contracts.Counter.VC.Inc
import Contracts.Counter.Spec.Export
import Contracts.Counter.Spec.ExportWrong
import Contracts.Counter.EndToEnd

/-!
# Counter: solar-verify's exported spec of `inc` from its erased tree, generically

The instance of `SolidCore.Spec.holdsFn_of_tree` for `Counter.inc`: the only per-function proof
is `inc_meets`, by `tree_meets` over the exported spec (`Export.Counter.Counter`) and the
generic stage's tree (`incTree`, `incShape_eq`), with no solver verdict and no binding to
solar-verify's encoding. `wrong_not_meets` is the negative: the spec mutant `x == old(x) + d + 1`
does not hold of the tree, by the call `inc(0)` from the empty storage.
-/

namespace SolidCore.Spec.TreeDemo.Counter

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Verify.VC.Counter

/-- The exported spec. -/
abbrev spec : Bundle := SolidCore.Spec.Export.Counter.Counter

/-- `inc`'s spec. -/
def incSpec : FnSpec := spec.spec.specs.head (by simp [spec, SolidCore.Spec.Export.Counter.Counter])

/-- The call context of the stage's calls (no value), as SolidCore's runs see it. -/
def ctx : Ctx := { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 }

/-- The call context of every call: `ctx` with the call's value. -/
def ctxOf (call : SolarTV.Call) : Ctx := { ctx with value := call.callvalue }

/-- **`inc`'s spec holds of its erased tree.** -/
theorem inc_meets : TreeMeets spec incSpec ctx 1 incTree := by
  tree_meets [incTree, incSpec, spec, SolidCore.Spec.Export.Counter.Counter]

/-- **`inc`'s spec holds of SolidCore's checked `Counter`** on the stage's calls of `inc`. -/
theorem inc_holds {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (step : GhostStep) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fnInc []) spec ctxOf step incSpec := by
  have hshape := incShape_eq
  simp only [incShape?, hc, Option.some.injEq, Prod.mk.injEq] at hshape
  obtain ⟨hdep, hmap⟩ := hshape
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact holdsFn_of_tree (fn := fnInc) hdd (by decide) hf hlen hT
    (fun call h => by simp [ctxOf, ctx, h]) inc_meets

/-- The mutant's spec of `inc`. -/
def mutSpec : FnSpec :=
  SolidCore.Spec.Export.CounterSpecMut.Counter.spec.specs.head
    (by simp [SolidCore.Spec.Export.CounterSpecMut.Counter])

/-- **The spec mutant does not hold of the tree**: `inc(0)` from the empty storage succeeds
with slot 0 still 0, and the mutant asks for 1. -/
theorem wrong_not_meets : ¬ TreeMeets SolidCore.Spec.Export.CounterSpecMut.Counter mutSpec ctx 1 incTree := by
  intro h
  have := (h [0] (fun _ => 0) [0] ⟨fun _ => 0, Ghost.zero, 0⟩ Ghost.zero rfl (by simp) (by simp)
    (by simp [mutSpec, SolidCore.Spec.Export.CounterSpecMut.Counter, decodeWords, Ty.ofWord])
    rfl (by simp [ctx]) (by simp [Bundle.satAll, mutSpec, SolidCore.Spec.Export.CounterSpecMut.Counter])
    (by simp [Bundle.satAll, SolidCore.Spec.Export.CounterSpecMut.Counter])).1
  simp [incTree, Tree.eval, WExpr.eval, BinOp.eval, Generic.wordSize, Res.obs, Writes.store,
    Bundle.satAll, Bundle.sat, eval, slotOf, mkEnv, Env.cur, BinOp.apply, Ty.ofBits, toWord,
    decodeWords, words, mutSpec, SolidCore.Spec.Export.CounterSpecMut.Counter] at this

/-- info: 'SolidCore.Spec.TreeDemo.Counter.inc_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_holds

/-- info: 'SolidCore.Spec.TreeDemo.Counter.wrong_not_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_not_meets

end SolidCore.Spec.TreeDemo.Counter

/-! ## The one theorem: the exported spec of `inc` holds of solar's bytecode -/

namespace SolidCore.Refinement.Solar.Counter.SpecTree

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Spec

/-- **solar-verify's exported spec of `inc` holds of solar's runtime bytecode** under EthLib, on
every call of `inc(uint256)` with any argument word, no value and any storage: the spec of the
erased tree (`inc_meets`, by evaluation), SolidCore's run of the tree (`holdsFn_of_tree`) and
the certified agreement of SolidCore's counter with the bytecode (`Verdict.agree`), with no
hypothesis and no solver verdict. -/
theorem inc_spec_bytecode (step : GhostStep) :
    ∃ c, contract? = .ok c ∧
      HoldsFn ethLib code (SolidCore.Verify.VC.stageScope SolidCore.Verify.VC.Counter.fnInc [])
        SolidCore.Spec.TreeDemo.Counter.spec SolidCore.Spec.TreeDemo.Counter.ctxOf step
        SolidCore.Spec.TreeDemo.Counter.incSpec := by
  obtain ⟨c, hc⟩ := contract_ok
  refine ⟨c, hc, (SolidCore.Spec.TreeDemo.Counter.inc_holds (by exact hc) step).of_stage ?_⟩
  exact fun call h obs hrun => (Verdict.agree hc).stage call (EndToEnd.inc_in_scope h) obs hrun

/-- info: 'SolidCore.Refinement.Solar.Counter.SpecTree.inc_spec_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inc_spec_bytecode

end SolidCore.Refinement.Solar.Counter.SpecTree
