import Verify.VC
import Verify.VC.KernelIdx
import Examples.Counter.VC.ExportMilestone
import SolidCore.Refinement.Solar.Counter.Source
import SolidCore.Refinement.KernelRfl

/-!
# solar-verify's `Counter.inc`, bound to the certified counter milestone

The contract is the one the certified translation covers: SolidCore's checked `Counter` from
`scripts/refinement/counter/counter.sol` (`contract` below is
`SolidCore.Refinement.Solar.Counter.contract?`'s body, so a proof of either equation is one of the
other). solar-verify reads `scripts/verify/CounterMilestone.sol`, the same text with one NatSpec line,
`ensures x == old(x) + d` (`check`.sh checks that stripping the `///` lines gives counter.sol back).

What is proved:
* `incShape_eq` (kernel): `Counter` deploys with no storage and no logs, and the generic source stage
  erases `inc(uint256)` to `incTree`.
* `inc_check` (kernel): solar-verify's script has an obligation that `checkOb` normalizes to
  `incHyps ⟹ incGoal`, written here by hand: its facts are the guard of `inc`'s success path
  (no value, `x + d` in range) and its goal states solar-verify's encoding `incEff` of the new `x`.
* `inc_binding`: a call of `inc` on `d` from storage `s` succeeds exactly when `incHyps` hold at the
  assignment `incEnv d s` it binds (`x` is slot 0, `d` the argument, `msg.value` 0), and then
  writes slot 0 with the value of `incEff` there and nothing else.
* `inc_triple`: on the stage's scope (any storage, any argument word, no value), `inc` succeeds
  exactly when `x + d < 2 ^ 256`, and then slot 0 holds `x + d` and every other slot is unchanged.

The goal of solar-verify's obligation for this clause, after its definition `arith = x + d` is
inlined, is `x + d = x + d`: valid by solar-verify's own encoding of the effect, so a verdict adds
nothing to it, and `inc_triple` takes no `Valid` premise. What ties solar-verify to SolidCore is the
binding: the effect solar-verify encodes is the one SolidCore runs, and the guard it assumes is
exactly SolidCore's success condition. The negatives (`CounterMutants`) show the check failing for
a one-line source mutant and a one-line spec mutant.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic SolidCore.Solidity SolidCore.Solidity.Source

/-- The interpreter fuel of SolidCore's runs. -/
def fuel : Nat := 4096

/-- SolidCore's checked `Counter`: `SolidCore.Refinement.Solar.Counter.contract?`'s body. -/
def contract? : Except TypeCheck.TypeError TypeCheck.CheckedContract :=
  TypeCheck.CheckedInput.contract SolidCore.Refinement.Source.Counter.importedSourceUnit "Counter"

/-- The selector of `inc(uint256)`. -/
abbrev incSel : Nat := 0x812600df

/-- The selector of `get()`. -/
abbrev getSel : Nat := 0x6d4ce63c

/-- The selector of `inc(uint256)`, by Keccak-256 of its signature. -/
def selInc : SolidCore.Solidity.Shared.Word := SolidCore.Solidity.Source.ABI.selectorFromSignature "inc(uint256)"

kernel_rfl selInc_eq selInc incSel

/-- The selector of `get()`, by Keccak-256 of its signature. -/
def selGet : SolidCore.Solidity.Shared.Word := SolidCore.Solidity.Source.ABI.selectorFromSignature "get()"

kernel_rfl selGet_eq selGet getSel

/-- `ABI.selectorFromSignature`, with `Counter`'s selectors by table. -/
def selectorTable (s : String) : SolidCore.Solidity.Shared.Word :=
  if s = "inc(uint256)" then incSel
  else if s = "get()" then getSel
  else SolidCore.Solidity.Source.ABI.selectorFromSignature s

theorem selector_eq : SolidCore.Solidity.Source.ABI.selectorFromSignature = selectorTable := by
  funext s
  unfold selectorTable
  by_cases h0 : s = "inc(uint256)"
  · rw [ite_eq_left h0, h0]
    exact selInc_eq
  rw [ite_eq_right h0]
  by_cases h1 : s = "get()"
  · rw [ite_eq_left h1, h1]
    exact selGet_eq
  rw [ite_eq_right h1]

/-- `inc(uint256)` as the stage's ABI sees it. -/
def fnInc : Fn := ⟨incSel, [.uint 256]⟩

/-- The revert data of `Panic(0x11)`, byte by byte. -/
def panic11 : List OByte :=
  [78, 72, 123, 113].map .lit ++ (List.replicate 31 (OByte.lit 0)) ++ [.lit 17]

/-- The erasure of `inc`: panic when `x + d` wraps, else write it to slot 0. -/
def incTree : Tree :=
  .ite (.bin .lt (.bin .add (.init 0) (.arg 0)) (.init 0)) (.halt false panic11 [] [])
    (.halt true [] [(.lit 0, .bin .add (.init 0) (.arg 0))] [])

/-- Whether `Counter` deploys with no storage and no logs, and how SolidCore dispatches `inc` and the
generic source stage erases it. -/
def incShape? : Option (Bool × Option (Nat × Option Tree)) :=
  match contract? with
  | .ok c => some (Wide.deployedAt fuel c [],
      (c.core.findFunctionBySelector? incSel).map fun f => (f.params.length, eraseFn (envOf c.core) fuel f))
  | .error _ => none

kernel_rfl incShape_eq incShape? (some (true, some (1, some incTree))) using selector_eq mkIdx_eq

/-! ## The Lean obligation -/

namespace Ob

def x : Tm := .ivar "x"
def d : Tm := .ivar "d"
def mv : Tm := .ivar "msg.value"
def ms : Tm := .ivar "msg.sender"
def le0 (t : Tm) : Tm := .app "<=" [.num 0, t]
def leW (t : Tm) : Tm := .app "<=" [t, .num (2 ^ 256 - 1)]
def add (a b : Tm) : Tm := .app "+" [a, b]
def eq (a b : Tm) : Tm := .app "=" [a, b]

end Ob

open Ob in
/-- solar-verify's encoding of `x` after `inc`. -/
def incEff : Tm := add x d

open Ob in
/-- The guard of `inc`'s success path, and the ranges of the words it reads. -/
def incHyps : List Tm :=
  [eq mv (.num 0), le0 incEff, leW incEff, le0 d, leW d, le0 x, leW x, le0 mv, leW mv,
    .app "not" [eq ms (.num 0)], le0 ms, .app "<=" [ms, .num (2 ^ 160 - 1)]]

open Ob in
/-- `inc`'s ensures clause as solar-verify states it, of its own encoding of the new `x`. -/
def incGoal : Tm := eq incEff (add x d)

/-- solar-verify's script for the annotated counter has an obligation that `checkOb` normalizes to
`incHyps ⟹ incGoal`. -/
theorem inc_check : checkScript Export.CounterMilestone.script [(incHyps, incGoal)] = true := by
  decide +kernel

/-! ## The binding -/

/-- The assignment of solar-verify's names that a call of `inc` on `d` from storage `s` binds. -/
def incEnv (d : Nat) (s : Storage) : Env :=
  ⟨fun y => if y = "x" then s 0 else if y = "d" then d else if y = "msg.sender" then callerWord else 0,
    fun _ => False, fun _ => fun _ => 0⟩

section
variable (d : Nat) (s : Storage)
@[simp] theorem incEnv_x : (incEnv d s).i "x" = s 0 := rfl
@[simp] theorem incEnv_d : (incEnv d s).i "d" = d := rfl
@[simp] theorem incEnv_mv : (incEnv d s).i "msg.value" = 0 := rfl
@[simp] theorem incEnv_ms : (incEnv d s).i "msg.sender" = 8192 := rfl
end

theorem incEff_eval (d : Nat) (s : Storage) : (incEff.eval (incEnv d s)).toInt = (s 0 : Int) + d := by
  simp [incEff, Ob.add, Ob.x, Ob.d, Tm.eval, Tm.evalList, applyOp, Value.toInt]

theorem incHyps_iff (d : Nat) (s : Storage) (hd : d < 2 ^ 256) (hs : s 0 < 2 ^ 256) :
    (∀ t ∈ incHyps, t.Holds (incEnv d s)) ↔ s 0 + d < 2 ^ 256 := by
  simp only [incHyps, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  simp [Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.toProp, Value.toInt, Value.eq, incEff, Ob.add,
    Ob.x, Ob.d, Ob.mv, Ob.ms, Ob.le0, Ob.leW, Ob.eq]
  omega

theorem incAdd_eval (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (d : Nat) (hd : d < 2 ^ 256) :
    (WExpr.bin .add (.init 0) (.arg 0)).eval (valOf [d] s) = (s 0 + d) % 2 ^ 256 := by
  simp [WExpr.eval, BinOp.eval, valOf, Generic.wordSize, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (hs 0)]

theorem incCond_eval (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (d : Nat) (hd : d < 2 ^ 256) :
    (WExpr.bin .lt (.bin .add (.init 0) (.arg 0)) (.init 0)).eval (valOf [d] s) =
      if s 0 + d < 2 ^ 256 then 0 else 1 := by
  have h := incAdd_eval s hs d hd
  simp only [WExpr.eval] at h ⊢
  rw [h]
  have h0 := hs 0
  simp only [BinOp.eval, valOf, Generic.wordSize, Nat.mod_eq_of_lt h0]
  by_cases hov : s 0 + d < 2 ^ 256
  · rw [Nat.mod_eq_of_lt hov, if_neg (by omega), if_pos hov]
  · have : (s 0 + d) % 2 ^ 256 = s 0 + d - 2 ^ 256 := by omega
    rw [this, if_pos (by omega), if_neg hov]

/-- The binding: a call of `inc` succeeds exactly when solar-verify's guard holds at the assignment
it binds, and then writes slot 0 with solar-verify's encoding of the new `x` and leaves every other
slot. -/
theorem inc_binding (s : Storage) (hs : ∀ k, s k < 2 ^ 256) (d : Nat) (hd : d < 2 ^ 256) :
    let R := incTree.eval (valOf [d] s)
    (R.success = true ↔ ∀ t ∈ incHyps, t.Holds (incEnv d s)) ∧
      (R.success = true → ((R.store 0 : Nat) : Int) = (incEff.eval (incEnv d s)).toInt ∧
        ∀ k, k % 2 ^ 256 ≠ 0 → R.store k = s k) := by
  intro R
  rw [incHyps_iff d s hd (hs 0), incEff_eval]
  have hc := incCond_eval s hs d hd
  have ha := incAdd_eval s hs d hd
  by_cases hov : s 0 + d < 2 ^ 256
  · have hsucc : R.success = true := by
      simp only [R, incTree, Tree.eval, hc, if_pos hov, ite_true]
    have hst : R.store = Writes.store (valOf [d] s) [(.lit 0, .bin .add (.init 0) (.arg 0))] := by
      simp only [R, incTree, Tree.eval, hc, if_pos hov, ite_true]
    refine ⟨by simp only [hsucc, true_iff]; omega, fun _ => ⟨?_, fun k hk => ?_⟩⟩
    · rw [hst]
      simp only [Writes.store, ha]
      split
      · rw [Nat.mod_eq_of_lt hov]; push_cast; rfl
      · rename_i h; exact absurd (by simp [WExpr.eval]) h
    · rw [hst]
      simp only [Writes.store]
      split
      · rename_i h; simp [WExpr.eval, Generic.wordSize] at h; omega
      · rfl
  · have hR : R.success = false := by
      simp only [R, incTree, Tree.eval, hc, if_neg hov]; rfl
    simp only [hR, Bool.false_eq_true, false_iff, false_implies, and_true]
    omega

/-- `inc`'s postcondition: it succeeds exactly when `x + d` does not wrap, and then slot 0 holds
`x + d` and every other slot is unchanged. -/
def incPost (call : Call) (obs : SolarTV.Observable) : Prop :=
  let d := (argWords 1 call).getD 0 0
  let s := initStorage call
  (obs.success = true ↔ s 0 + d < 2 ^ 256) ∧
    (obs.success = true → obs.storage 0 = s 0 + d ∧ ∀ k, k % 2 ^ 256 ≠ 0 → obs.storage k = s k)

theorem vc_eq (model : List Nat → SolM (List Nat)) (args : Call → List Nat)
    (post : Call → SolarTV.Observable → Prop) (call : Call) :
    vc model args post call =
      post call (observe (initStorage call) (model (args call) (initStorage call))) := by
  unfold vc
  rw [wp_eq]
  rcases h : model (args call) (initStorage call) with e | ⟨out, s'⟩ <;> simp only [h] <;> rfl

/-- `Counter.inc` on the stage's scope: it succeeds exactly when `x + d` does not wrap, and then slot 0
holds `x + d` and every other slot is unchanged, through `implementsTree` and the binding to
solar-verify's encoding. -/
theorem inc_triple {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnInc []) (fun _ => True) incPost := by
  have hshape := incShape_eq
  simp only [incShape?, hc, Option.some.injEq, Prod.mk.injEq] at hshape
  obtain ⟨hdep, hmap⟩ := hshape
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  have himpl := implements_tree (fn := fnInc) hdd (by decide) hf hlen hT rfl
  apply triple_of_wp himpl
  rintro _ ⟨σ, -, fn', hfn', args, hl, hargs, rfl⟩ -
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  obtain ⟨d, rfl⟩ : ∃ d, args = [d] := by
    match args, hl with
    | [d], _ => exact ⟨d, rfl⟩
  have hd : d < 2 ^ 256 := hargs d (List.mem_singleton_self d)
  have hw : argWords 1 ({ calldata := Abi.calldata fnInc.sel [d], callvalue := 0, storage := σ } : Call) =
      [d] := argWords_calldata _ [d] hargs 0 σ
  rw [vc_eq, treeModel_run, show fnInc.params.length = 1 from rfl, hw]
  set s := initStorage ({ calldata := Abi.calldata fnInc.sel [d], callvalue := 0, storage := σ } : Call)
    with hs_def
  have hs : ∀ k, s k < 2 ^ 256 := fun k => Generic.slotValue_lt σ k
  obtain ⟨hiff, hok⟩ := inc_binding s hs d hd
  have hguard := incHyps_iff d s hd (hs 0)
  simp only [incPost, hw, List.getD_cons_zero, ← hs_def]
  unfold resOutcome
  split
  · next hsucc =>
    obtain ⟨h0, hk⟩ := hok hsucc
    rw [incEff_eval] at h0
    simp only [observe, true_iff]
    refine ⟨hguard.mp (hiff.mp hsucc), fun _ => ⟨?_, hk⟩⟩
    omega
  · next hfail =>
    simp only [observe, Bool.false_eq_true, false_iff, false_implies, and_true]
    intro hlt
    exact hfail (hiff.mpr (hguard.mpr hlt))

/-- info: 'SolidCore.Verify.VC.Counter.inc_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_triple

/-- info: 'SolidCore.Verify.VC.Counter.inc_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_check

end SolidCore.Verify.VC.Counter
