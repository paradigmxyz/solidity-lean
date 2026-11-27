import Verify.Spec.Tree
import Verify.ShapeSpecExport
import Verify.LoopSource.Generic.Statement

/-!
# solar-verify's exported spec on the erased tree of a loop function

The loop route (`Verify.LoopSource.Equiv.LeastFuel.eraseLoop_certified`,
`eraseLoop_certified_loops`) publishes the driver's `Shapes.Certified` for a one-loop function
once its allowed statuses and its postcondition hold of the tree `T` that `brTree` makes of the
loop erasure (`OnTree sel fn ws T Allowed`, `OnTree sel fn ws T Post`). The generic source stage
does not erase such a function (`eraseFn` is `none`), so `holdsFn_of_tree` (Tree.lean), which
goes through `eraseFn`, does not apply to it.

This module gives those two premises for the statement's specification, solar-verify's export
(`Shapes.bundlePost b ctxOf step`, `Shapes.bundleAllowed b ctxOf`), from the same tree-only
obligation the generic stage's functions discharge, `TreeMeets` (or `TreeMeetsFixed` when the
ghost step is the identity on the function's calls), of every function spec of the function's
selector, on the erased tree:

* `onTree_post`: `TreeMeets` of every function spec of the selector, at the context `ctxOf`
  gives every valid call (`selCall sel σ args`), is `OnTree` of `bundlePost` for every ghost step;
* `onTree_post_fixed`: the same from `TreeMeetsFixed`, for a step that leaves the ghost state alone
  on the valid calls (such as `Shapes.idStep`);
* `allowed_of_post`, `onTree_allowed`: `bundlePost` implies `bundleAllowed` pointwise, so the
  allowed statuses follow from the postcondition;
* `onTree_ctxOfCall`, `onTree_ctxOfCall_fixed`: both premises at once for the driver's
  `Shapes.ctxOfCall` and `Shapes.idStep`, at the context of the stage's calls, `ctx0`.

Function specs of other selectors impose nothing on a valid call, since their precondition's
selector differs (`pre_selCall`). Nothing here names a contract.

**The frame is fixed.** A valid call is `selCall sel σ args`: clean calldata of the selector and
argument words below `2 ^ 256`, any storage `σ`, and the one context `ctx0` that
`Shapes.ctxOfCall` gives it: sender `0x2000`, value 0, timestamp 1, self `0x1000`. Nothing here
speaks of another caller, a value, another block or deployment; those are Phase 2.

**No vacuous spec.** With no function spec of the selector, `OnTree` of the export holds of any
tree, since nothing constrains the call. `selOnly b sel i` therefore asks that the spec at index
`i` has the selector (and no other does): the empty bundle, or any bundle without a spec of `sel`,
fails it (`selOnly_nil`, `has_of_selOnly`).
-/

namespace SolidCore.Spec.TreeLoop

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity.Source
open Verify.LoopSource.Generic
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed ctxOfCall idStep selectorOf_calldata)

/-- The call context `Shapes.ctxOfCall` gives every call without a value, as spec_connect's `ctx`. -/
def ctx0 : Ctx := { sender := 0x2000, value := 0, timestamp := 1, self := 0x1000 }

theorem ctxOfCall_selCall (sel : Nat) (σ : List (Nat × Nat)) (args : List Nat) :
    ctxOfCall (selCall sel σ args) = ctx0 := rfl

/-- What a valid call's precondition gives: the selector, the decoded arguments of its words, the
pre-state's storage, the time and the requires and invariants. -/
theorem pre_selCall {b : Bundle} {fs : FnSpec} {ctx : Ctx} {pre : State} {sel : Nat}
    (hsel : sel < 2 ^ 32) {σ : List (Nat × Nat)} {args : List Nat} (hargs : ∀ a ∈ args, a < 2 ^ 256)
    {iargs : List Int} (h : Pre b fs ctx pre (selCall sel σ args) iargs) :
    fs.selector = sel ∧ decodeWords fs.params args = some iargs ∧ pre.storage = slotValue σ ∧
      pre.time ≤ ctx.timestamp ∧ b.satAll fs.requires (mkEnv ctx iargs [] pre pre) ∧
      b.satAll b.spec.invariants (mkEnv ctx iargs [] pre pre) := by
  obtain ⟨⟨-, hs, hdec⟩, hst, ht, hreq, hinv⟩ := h
  refine ⟨?_, ?_, hst, ht, hreq, hinv⟩
  · exact hs.symm.trans (selectorOf_calldata hsel args 0 σ)
  · change decodeWords fs.params (words (((Abi.calldata sel args).data.toList.map (·.toNat)).drop 4))
      = some iargs at hdec
    rwa [words_calldata sel hargs] at hdec

/-- **The exported postcondition on the erased tree**, from `TreeMeets` of every function spec of the
selector at the valid calls' context, for every ghost step. -/
theorem onTree_post {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T : Tree}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx} (hsel : sel < 2 ^ 32)
    (hctx : ∀ σ args, ctxOf (selCall sel σ args) = ctx)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeets b fs ctx fn.params.length T) :
    OnTree sel fn ws T (bundlePost b ctxOf step) := by
  rintro σ args ⟨hl, hargs, -⟩ fs hfs iargs pre hpre
  rw [hctx] at hpre ⊢
  obtain ⟨hs, hdec, hst, ht, hreq, hinv⟩ := pre_selCall hsel hargs hpre
  exact hm fs hfs hs args (slotValue σ) iargs pre _ hl hargs (fun k => slotValue_lt σ k) hdec hst ht
    hreq hinv

/-- **The same from `TreeMeetsFixed`**, for a ghost step that leaves the ghost state alone on the
valid calls. -/
theorem onTree_post_fixed {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T : Tree}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx} (hsel : sel < 2 ^ 32)
    (hctx : ∀ σ args, ctxOf (selCall sel σ args) = ctx)
    (hstep : ∀ σ args g, step (selCall sel σ args) g = g)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeetsFixed b fs ctx fn.params.length T) :
    OnTree sel fn ws T (bundlePost b ctxOf step) := by
  rintro σ args ⟨hl, hargs, -⟩ fs hfs iargs pre hpre
  rw [hctx] at hpre ⊢
  rw [hstep]
  obtain ⟨hs, hdec, hst, ht, hreq, hinv⟩ := pre_selCall hsel hargs hpre
  exact hm fs hfs hs args (slotValue σ) iargs pre hl hargs (fun k => slotValue_lt σ k) hdec hst ht
    hreq hinv

/-- **The exported postcondition gives the exported allowed statuses**: a revert from a pre-state
meeting a function spec's succeeds-if conditions contradicts that spec's `Post`. -/
theorem allowed_of_post {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep} {call : Call}
    {obs : Observable} (h : bundlePost b ctxOf step call obs) : bundleAllowed b ctxOf call obs := by
  by_cases hs : obs.success = true
  · exact Or.inl hs
  · exact Or.inr fun fs hfs args pre hpre hne hsat => hs ((h fs hfs args pre hpre).2 hne hsat)

theorem onTree_allowed {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T : Tree}
    {ctxOf : Call → Ctx} {step : GhostStep} (h : OnTree sel fn ws T (bundlePost b ctxOf step)) :
    OnTree sel fn ws T (bundleAllowed b ctxOf) :=
  fun σ args ha => allowed_of_post (h σ args ha)

/-- **Both premises of the loop route for the driver's specification** (`Shapes.ctxOfCall`,
`Shapes.idStep`), from `TreeMeets` at `ctx0` of every function spec of the selector. -/
theorem onTree_ctxOfCall {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T : Tree}
    (hsel : sel < 2 ^ 32)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeets b fs ctx0 fn.params.length T) :
    OnTree sel fn ws T (bundleAllowed b ctxOfCall) ∧ OnTree sel fn ws T (bundlePost b ctxOfCall idStep) :=
  have h := onTree_post (step := idStep) hsel (ctxOfCall_selCall sel) hm
  ⟨onTree_allowed h, h⟩

/-- The same from `TreeMeetsFixed`. -/
theorem onTree_ctxOfCall_fixed {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat} {T : Tree}
    (hsel : sel < 2 ^ 32)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel → TreeMeetsFixed b fs ctx0 fn.params.length T) :
    OnTree sel fn ws T (bundleAllowed b ctxOfCall) ∧ OnTree sel fn ws T (bundlePost b ctxOfCall idStep) :=
  have h := onTree_post_fixed (step := idStep) hsel (ctxOfCall_selCall sel) (fun _ _ _ => rfl) hm
  ⟨onTree_allowed h, h⟩

/-- The spec at index `i` is of selector `sel` and no other spec is: `hm` of `onTree_ctxOfCall`
from the spec at one index (the form spec_connect.py writes: `F_meets` of the spec at `F`'s index,
and `selOnly` by evaluation). A bundle with no spec of `sel` fails it. -/
def selOnly (b : Bundle) (sel i : Nat) : Bool :=
  (b.spec.specs[i]?.map (·.selector) == some sel) &&
    (List.range b.spec.specs.length).all fun j => (b.spec.specs.getD j default).selector != sel || j == i

/-- **The chosen index has the selector.** -/
theorem selOnly_get {b : Bundle} {sel i : Nat} (h : selOnly b sel i = true) :
    ∃ hi : i < b.spec.specs.length, b.spec.specs[i].selector = sel := by
  simp only [selOnly, Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  cases hx : b.spec.specs[i]? with
  | none => simp [hx] at h1
  | some fs =>
    obtain ⟨hi, hfs⟩ := List.getElem?_eq_some_iff.mp hx
    simp only [hx, Option.map_some, beq_iff_eq, Option.some.injEq] at h1
    exact ⟨hi, hfs ▸ h1⟩

/-- **`selOnly` needs a spec of the selector.** -/
theorem has_of_selOnly {b : Bundle} {sel i : Nat} (h : selOnly b sel i = true) :
    ∃ fs ∈ b.spec.specs, fs.selector = sel :=
  have ⟨hi, hs⟩ := selOnly_get h
  ⟨_, List.getElem_mem hi, hs⟩

/-- **The empty bundle fails `selOnly`**, at every selector and index. -/
theorem selOnly_nil {b : Bundle} (h : b.spec.specs = []) (sel i : Nat) : selOnly b sel i = false := by
  simp [selOnly, h]

theorem meets_of_index {b : Bundle} {sel : Nat} {P : FnSpec → Prop} (i : Nat)
    (hi : i < b.spec.specs.length) (honly : selOnly b sel i = true) (h : P b.spec.specs[i]) :
    ∀ fs ∈ b.spec.specs, fs.selector = sel → P fs := by
  intro fs hfs hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hfs
  simp only [selOnly, Bool.and_eq_true] at honly
  have hk := List.all_eq_true.mp honly.2 j (List.mem_range.mpr hj)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hk
  simp only [hs, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hk
  subst hk
  exact h

end SolidCore.Spec.TreeLoop

/-- info: 'SolidCore.Spec.TreeLoop.onTree_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.onTree_post

/-- info: 'SolidCore.Spec.TreeLoop.onTree_ctxOfCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.onTree_ctxOfCall

/-- info: 'SolidCore.Spec.TreeLoop.onTree_ctxOfCall_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.onTree_ctxOfCall_fixed

/-- info: 'SolidCore.Spec.TreeLoop.meets_of_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.meets_of_index

/-- info: 'SolidCore.Spec.TreeLoop.has_of_selOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.has_of_selOnly

/-- info: 'SolidCore.Spec.TreeLoop.selOnly_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.TreeLoop.selOnly_nil
