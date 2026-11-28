import Verify.Spec.Tree
import Verify.Generic.CtorWords

/-!
# A spec from the erased tree, for the contract deployed with any constructor arguments

`holdsFn_of_tree` (Tree.lean) states a function's spec against `solidCore fuel`: the contract
deployed by its constructor run with **no arguments** (`Wide.DeployedAt`). A constructor with word
parameters has no such run. This module states the same connection against
`solidCoreFromArgs callerAddress fuel ws` (StageFrom.lean: the constructor on the argument words
`ws`, then the call):

* `holdsFn_of_tree_args` and `holdsFn_of_tree_fixed_args`: from a load-level deployment on `ws`
  (`Loop.LoadDeployed`) and a storage list `s` every cover of which gives its load cover, a spec
  that holds of the erased tree (`TreeMeets`, `TreeMeetsFixed`) holds of the contract deployed with
  `ws` on the stage's calls of the function (`stageScope fn s`).
* `holdsFn_of_tree_ctorShape` and `holdsFn_of_tree_fixed_ctorShape`: the same **for every argument
  list** on which the constructor returns, from the kernel-evaluated constructor shape
  (`ctorShapeOf`, CtorWords.lean): the deployed storage is `storageOf W ws`, a function of the
  words.

The tree and its `TreeMeets` proof do not mention the deployment: they hold from any storage, so the
proof `tree_meets` writes for the no-argument route serves every argument list unchanged.
-/

namespace SolidCore.Spec

open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- **A function's spec holds of the contract deployed with the argument words `ws` when it holds
of the erased tree**, on the stage's calls of the function from any storage covering `s`, whose
covers give the deployment's load cover. -/
theorem holdsFn_of_tree_args {fuel : Nat} {c : TypeCheck.CheckedContract} {ws : List Nat}
    {d : Source.State} (hd : Loop.LoadDeployed fuel c ws d) {s : List (Nat × Nat)}
    (hcov : ∀ σ, Covers s σ → Loop.CoversLoad d σ) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    HoldsFn (solidCoreFromArgs callerAddress fuel ws) c (SolidCore.Verify.VC.stageScope fn s) b
      ctxOf step fs :=
  holdsFn_of_tree_run (fun σ hc args hl hargs =>
    source_run_args hd (hcov σ hc) hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun _ _ args st iargs pre => hm args st iargs pre _

/-- `holdsFn_of_tree_args` for a function that leaves the ghost state alone. -/
theorem holdsFn_of_tree_fixed_args {fuel : Nat} {c : TypeCheck.CheckedContract} {ws : List Nat}
    {d : Source.State} (hd : Loop.LoadDeployed fuel c ws d) {s : List (Nat × Nat)}
    (hcov : ∀ σ, Covers s σ → Loop.CoversLoad d σ) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    HoldsFn (solidCoreFromArgs callerAddress fuel ws) c (SolidCore.Verify.VC.stageScope fn s) b
      ctxOf step fs :=
  holdsFn_of_tree_run (fun σ hc args hl hargs =>
    source_run_args hd (hcov σ hc) hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun call hcall args st iargs pre => by
      rw [hstep call hcall pre.ghost]; exact hm args st iargs pre

/-- **A function's spec holds of the contract deployed with every argument list on which its
constructor returns**, from the kernel-evaluated constructor shape: on each such `ws`, on the
stage's calls of the function from any storage covering `storageOf W ws`. -/
theorem holdsFn_of_tree_ctorShape {fuel : Nat}
    {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract} {wds : List Nat} {br : Br}
    {W : Writes} {core : Source.Contract} {c : TypeCheck.CheckedContract}
    (hshape : ctorShapeOf fuel c? wds br W = some (core, true)) (hc : c? = .ok c) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    ∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
      CtorReturns fuel c? ws →
      HoldsFn (solidCoreFromArgs callerAddress fuel ws) c
        (SolidCore.Verify.VC.stageScope fn (storageOf W ws)) b ctxOf step fs := by
  intro ws hl ha hcl hret
  obtain ⟨d, hd, hcov⟩ := (deployed_of_ctorShapeOf hshape hc).2.1 ws hl ha hcl hret
  exact holdsFn_of_tree_args hd hcov hsel hfind hlen hT hctx hm

/-- `holdsFn_of_tree_ctorShape` for a function that leaves the ghost state alone. -/
theorem holdsFn_of_tree_fixed_ctorShape {fuel : Nat}
    {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract} {wds : List Nat} {br : Br}
    {W : Writes} {core : Source.Contract} {c : TypeCheck.CheckedContract}
    (hshape : ctorShapeOf fuel c? wds br W = some (core, true)) (hc : c? = .ok c) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    ∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
      CtorReturns fuel c? ws →
      (∀ call, SolidCore.Verify.VC.stageScope fn (storageOf W ws) call → ∀ g, step call g = g) →
      HoldsFn (solidCoreFromArgs callerAddress fuel ws) c
        (SolidCore.Verify.VC.stageScope fn (storageOf W ws)) b ctxOf step fs := by
  intro ws hl ha hcl hret hstep
  obtain ⟨d, hd, hcov⟩ := (deployed_of_ctorShapeOf hshape hc).2.1 ws hl ha hcl hret
  exact holdsFn_of_tree_fixed_args hd hcov hsel hfind hlen hT hctx hstep hm

/-- info: 'SolidCore.Spec.holdsFn_of_tree_ctorShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_ctorShape

/-- info: 'SolidCore.Spec.holdsFn_of_tree_fixed_ctorShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_of_tree_fixed_ctorShape

end SolidCore.Spec
