import Verify.Spec.TreeFrom
import Verify.LoopSource.Equiv.LoopFrom
import Verify.LoopSource.Generic.Statement
import Verify.Generic.Expected
import Verify.ShapeBundle
import Verify.ShapeSpecExport

/-!
# Phase 2, first slice: a loop function's property from every caller

`Verify/Spec/TreeLoop.lean` reads solar-verify's exported spec on a loop function's erased tree at
one call context, `ctx0` (sender `0x2000`, value 0, timestamp 1, contract `0x1000`), with the tree at
the constant caller word `callerWord`. This module states the same property for **every caller**:
the tree is evaluated for the caller `a` and the spec is read in `a`'s own context
`ctxOfCallFrom a` (`= ctxAt a 0` on a call without value), for every `a < 2 ^ 160` other than the
contract. The caller is a hypothesis of every statement, never a literal.

It is the property half only. Translation (the bytecode's run from `a` is the source's run from
`a`) is a separate theorem per contract (for Counter, `Verify.Phase2.CounterCaller`), and nothing
here uses it.

* `OnTreeAt a`: `OnTree` (Verify/LoopSource/Generic/Statement.lean) with the tree evaluated for `a`.
* `onTreeAt_post`: `TreeMeetsFixedAt a` (Verify/Spec/TreeFrom.lean) of every function spec of the
  selector, in `ctxAt a 0`, gives `OnTreeAt a` of `bundlePost` at `ctxOfCallFrom a`.
* `property_from`: **the property from every caller, on the source.** For a function whose body
  runs to a tree from every caller (`BodyRunsFrom`, the loop route's product), `TreeMeetsFixedAt a`
  for every caller gives: every result of SolidCore's runtime code sent by `a` on a valid call (no
  value) meets `bundlePost` and `bundleAllowed` in `a`'s context.
* `fail_meets`: a failing result meets both, for a spec without succeeds-if conditions: the
  property half of a non-payable function's calls with a value (which the dispatcher rejects).

`pre_sel` and `allowed_of_post'` restate two short lemmas of TreeLoop.lean (`pre_selCall`,
`allowed_of_post`) at no fixed context, since that module is not yet built.
-/

namespace Verify.Phase2.CallerFrom

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Solidity
open SolidCore.Solidity.Source SolidCore.Spec SolidCore.Verify.AnyCaller Verify.LoopSource.Generic
open SolidCore.Refinement.Generic.Loop
open SolidCore.Refinement.Shapes (bundlePost bundleAllowed idStep selectorOf_calldata)

/-- `Q` holds of the tree's observable for the caller `a` on every valid call. -/
def OnTreeAt (a sel : Nat) (fn : FunctionDef) (ws : List Nat) (T : Tree)
    (Q : Call → Observable → Prop) : Prop :=
  ∀ (σ : List (Nat × Nat)) args, ArgsOk fn ws args →
    Q (selCall sel σ args) (T.eval ⟨args, slotValue σ, solHash, a⟩).obs

/-- A call without value sent by `a` is read in `ctxAt a 0`. -/
theorem ctxOfCallFrom_selCall (a sel : Nat) (σ : List (Nat × Nat)) (args : List Nat) :
    ctxOfCallFrom a (selCall sel σ args) = ctxAt a 0 := rfl

/-- What a valid call's precondition gives, in any context. -/
theorem pre_sel {b : Bundle} {fs : FnSpec} {ctx : Ctx} {pre : SolidCore.Spec.State} {sel : Nat}
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

/-- `bundlePost` gives `bundleAllowed`, pointwise. -/
theorem allowed_of_post' {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep} {call : Call}
    {obs : Observable} (h : bundlePost b ctxOf step call obs) : bundleAllowed b ctxOf call obs := by
  by_cases hs : obs.success = true
  · exact Or.inl hs
  · exact Or.inr fun fs hfs args pre hpre hne hsat => hs ((h fs hfs args pre hpre).2 hne hsat)

/-- **The exported postcondition on the tree, for the caller `a`**, from `TreeMeetsFixedAt a` of
every function spec of the selector in `a`'s context. -/
theorem onTreeAt_post {a : Nat} {b : Bundle} {sel : Nat} {fn : FunctionDef} {ws : List Nat}
    {T : Tree} (hsel : sel < 2 ^ 32)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel →
      TreeMeetsFixedAt a b fs (ctxAt a 0) fn.params.length T) :
    OnTreeAt a sel fn ws T (bundlePost b (ctxOfCallFrom a) idStep) := by
  rintro σ args ⟨hl, hargs, -⟩ fs hfs iargs pre hpre
  obtain ⟨hs, hdec, hst, ht, hreq, hinv⟩ := pre_sel hsel hargs hpre
  exact hm fs hfs hs args (slotValue σ) iargs pre hl hargs (fun k => Generic.slotValue_lt σ k) hdec
    hst ht hreq hinv

/-- **Property satisfaction for one caller `a`, on the source (generic).** A function `fn` at
selector `sel` with word arguments of widths `ws` and word returns, whose body runs to the tree of
`br` from every caller (`BodyRunsFrom`), and whose tree meets every function spec of its selector
for the caller `a < 2 ^ 160` in `a`'s context: every result of SolidCore's runtime code sent by `a`
on a valid call (any storage, clean argument words, no value) meets the exported postcondition and
allowed statuses read in `a`'s context. -/
theorem property_at {fuel : Nat} {c : TypeCheck.CheckedContract} {sel : Nat}
    (hsel : sel < 2 ^ 32) {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    {ws : List Nat} (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {br : Br}
    (hb : BodyRunsFrom { envOf c.core with facts := argFacts ws 0 } fuel fn br)
    {T : Tree} (hT : brTree fn (argFacts ws 0) br = some T) {b : Bundle} {a : Nat} (ha : a < 2 ^ 160)
    (hm : ∀ fs ∈ b.spec.specs, fs.selector = sel →
      TreeMeetsFixedAt a b fs (ctxAt a 0) fn.params.length T) :
    ∀ call, SelCall sel fn ws call →
      ∀ obs, (solidCoreRuntimeFrom a fuel).run c call = some obs →
        bundlePost b (ctxOfCallFrom a) idStep call obs ∧ bundleAllowed b (ctxOfCallFrom a) call obs := by
  rintro _ ⟨σ, args, ⟨hl, hargs, hclean⟩, rfl⟩ obs hrun
  have hdec := decode_args hw args hl hargs
  rw [if_pos hclean] at hdec
  have h := runtime_run_clean_from a ha (σ := σ) hsel hfind hw hret hb hT args hl hargs hclean hdec
  have hrun' : runtimeRunFrom a fuel c (selCall sel σ args) = some obs := hrun
  rw [show selCall sel σ args = { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }
    from rfl, h] at hrun'
  obtain rfl := Option.some.inj hrun'
  have hp := onTreeAt_post (ws := ws) hsel hm σ args ⟨hl, hargs, hclean⟩
  exact ⟨hp, allowed_of_post' hp⟩

/-- **Property satisfaction from every caller, on the source (generic).** `property_at` for every
caller `a < 2 ^ 160` other than the contract, each read in its own context. -/
theorem property_from {fuel : Nat} {c : TypeCheck.CheckedContract} {sel : Nat}
    (hsel : sel < 2 ^ 32) {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    {ws : List Nat} (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {br : Br}
    (hb : BodyRunsFrom { envOf c.core with facts := argFacts ws 0 } fuel fn br)
    {T : Tree} (hT : brTree fn (argFacts ws 0) br = some T) {b : Bundle}
    (hm : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ fs ∈ b.spec.specs, fs.selector = sel →
      TreeMeetsFixedAt a b fs (ctxAt a 0) fn.params.length T) :
    ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, SelCall sel fn ws call →
      ∀ obs, (solidCoreRuntimeFrom a fuel).run c call = some obs →
        bundlePost b (ctxOfCallFrom a) idStep call obs ∧ bundleAllowed b (ctxOfCallFrom a) call obs :=
  fun a ha hne => property_at hsel hfind hw hret hb hT ha (hm a ha hne)

/-- **A failing result meets the exported spec**, when no function spec has succeeds-if
conditions, in any context: the property half of a call a non-payable function rejects. -/
theorem fail_meets {b : Bundle} (hno : ∀ fs ∈ b.spec.specs, fs.succeedsIf = [])
    (ctxOf : Call → Ctx) (step : GhostStep) (call : Call) {obs : Observable}
    (hf : obs.success = false) :
    bundlePost b ctxOf step call obs ∧ bundleAllowed b ctxOf call obs := by
  refine ⟨fun fs hfs args pre _ => ⟨fun hs => ?_, fun hne => absurd (hno fs hfs) hne⟩,
    Or.inr fun fs hfs _ _ _ hne => absurd (hno fs hfs) hne⟩
  rw [hf] at hs
  exact absurd hs (by decide)

end Verify.Phase2.CallerFrom

/-- info: 'Verify.Phase2.CallerFrom.property_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerFrom.property_from

/-- info: 'Verify.Phase2.CallerFrom.fail_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CallerFrom.fail_meets
