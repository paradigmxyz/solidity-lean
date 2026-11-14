import Verify.Spec.Tree
import SolidCore.Refinement.Generic.StageIn

/-!
# Tree specs in every world

`TreeMeets` speaks of a function's erased tree alone, so it says nothing about the world a call
runs in. SolidCore runs a call of a function of the generic stage's fragment as its tree in every
world `W` (`Generic.source_runIn`): a call-free function asks the world nothing. So a spec proved
of the tree (`tree_meets`, `tree_meets_map`) holds of SolidCore in every world, open or not
(`holdsFn_of_tree_in`, `holdsFn_of_tree_fixed_in`), which is what `compose_in` and
`holds_of_runs` (Verify/SourceOracle.lean) take for the source side. The closed world is
`holdsFn_of_tree` again (`solidCoreIn_closed`).
-/

namespace SolidCore.Spec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- **A function's spec holds of SolidCore's contract in every world when it holds of the erased
tree**, on the stage's calls of the function. -/
theorem holdsFn_of_tree_in (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    HoldsFn (solidCoreIn W fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs := by
  rintro _ ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ iargs pre hpre
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hrun := source_runIn W hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hctx _ rfl] at ht hreq hinv ⊢
  rw [words_calldata _ hargs] at hdec
  exact ⟨_, hrun, hm args (slotValue σ) iargs pre _ hl hargs (fun k => Generic.slotValue_lt σ k)
    hdec hst ht hreq hinv⟩

/-- `holdsFn_of_tree_in` for a function that leaves the ghost state alone. -/
theorem holdsFn_of_tree_fixed_in (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    HoldsFn (solidCoreIn W fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs := by
  intro call hcall iargs pre hpre
  have hg := hstep call hcall pre.ghost
  obtain ⟨σ, hcov, fn', hfn', args, hl, hargs, rfl⟩ := hcall
  simp only [List.mem_singleton] at hfn'
  subst hfn'
  have hrun := source_runIn W hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs
  obtain ⟨⟨-, -, hdec⟩, hst, ht, hreq, hinv⟩ := hpre
  rw [hctx _ rfl] at ht hreq hinv ⊢
  rw [words_calldata _ hargs] at hdec
  rw [hg]
  exact ⟨_, hrun, hm args (slotValue σ) iargs pre hl hargs (fun k => Generic.slotValue_lt σ k)
    hdec hst ht hreq hinv⟩

/-- info: 'SolidCore.Spec.holdsFn_of_tree_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_in

/-- info: 'SolidCore.Spec.holdsFn_of_tree_fixed_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_fixed_in

end SolidCore.Spec
