import Verify.Generic.Unroll
import Verify.ShapeSpecExport
import Verify.Spec.TreeIn

/-!
# Specifications of functions with unrolled loops

`Verify/Generic/Unroll.lean` states the generic source stage for functions whose loops run a number
of iterations their own words fix, from `Generic.eraseFnL` (`source_runL`). A function's exported
specification is connected to SolidCore through its erased tree (`Verify/Spec/Tree.lean`,
`holdsFn_of_tree_run`): this module gives the same connection from the unrolled tree.

* `Generic.source_runInL`: `source_runIn` (SolidCore in every world `W`) for `eraseFnL`.
* `SolidCore.Spec.holdsFn_of_treeL`, `holdsFn_of_tree_fixedL`, `holdsFn_of_tree_inL`,
  `holdsFn_of_tree_fixed_inL`: `holdsFn_of_tree`, `holdsFn_of_tree_fixed` and their `_in` forms
  with `eraseFnL` (`source_runL`, `source_runInL` as the run).
* `Shapes.run_valueL`, `Shapes.holdsFn_genericValidL`: `run_value` and `holdsFn_genericValid` from
  `checkL` (a call with a value reverts with empty data).

Each conclusion is the original theorem's, word for word.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-- **SolidCore in every world runs a call as its unrolled erased tree**: `source_runIn` for
`eraseFnL`, whose proof is `source_runIn_clean`'s and `source_runIn`'s with `runs_eraseLoopCall` as
the body's run. -/
theorem source_runInL (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.runIn W fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold eraseFnL at hT
  split at hT
  · simp at hT
  rename_i ws hw
  split at hT
  case isFalse => simp at hT
  rename_i hret'
  obtain ⟨hret, htags⟩ := Bool.and_eq_true _ _ ▸ hret'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hT
  obtain ⟨b, hb, t, ht, rfl⟩ := hT
  rw [paramGuards_eval ⟨args, slotValue σ, solHash, callerWord⟩ t hargs ws 0, List.drop_zero]
  have hdec := decode_argsT hw args hlen hargs
  by_cases hclean : argsClean ws args = true
  · rw [if_pos hclean]
    rw [if_pos hclean] at hdec
    rw [SolidCore.Refinement.Wide.callAt_of_args sel args hargs σ,
      runIn_eq_at W hd, SolidCore.Refinement.Wide.map_ofNat_toNat args hargs]
    obtain ⟨⟨R, hR⟩, hobs⟩ := abi_clean hsel hfind hw hret fuel (ctxIn W c) callerAddress
      (st0 := { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage })
      (getD_storage_cover hd hcov) hd.events (.lit callerWord) hlen hargs
      (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)) rfl
      htags hdec ht (fun rt hrel => Loop.runs_eraseLoopCall _ _ fuel fn.body _ b hb _ rt hrel)
      (Wide.callAt sel (args.map (BitVec.ofNat 256)) σ) rfl
    rw [callCalldata_done W.ans hsel hfind hdec ((call_tyVals hw hlen hargs _ _ _ _).trans hR)]
    exact hobs
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [runIn_rejected W hd hsel hfind args hargs hdec σ]
    rfl

end SolidCore.Refinement.Generic

namespace SolidCore.Spec
open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic
open SolidCore.Solidity

/-- `holdsFn_of_tree_in` for `eraseFnL`: a function's spec from its unrolled tree in every world. -/
theorem holdsFn_of_tree_inL (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    HoldsFn (solidCoreIn W fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs :=
  holdsFn_of_tree_run (fun _ hcov args hl hargs =>
    source_runInL W hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun _ _ args st iargs pre => hm args st iargs pre _

/-- `holdsFn_of_tree_fixed_in` for `eraseFnL`. -/
theorem holdsFn_of_tree_fixed_inL (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn}
    {f : Source.FunctionDef} (hsel : fn.sel < 2 ^ 32)
    (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    HoldsFn (solidCoreIn W fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs :=
  holdsFn_of_tree_run (fun _ hcov args hl hargs =>
    source_runInL W hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun call hcall args st iargs pre => by
      rw [hstep call hcall pre.ghost]; exact hm args st iargs pre

/-- **A function's spec from its unrolled tree**: `holdsFn_of_tree` for `eraseFnL`. -/
theorem holdsFn_of_treeL {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hm : TreeMeets b fs ctx fn.params.length T) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs :=
  holdsFn_of_tree_run (fun _ hcov args hl hargs =>
    source_runL hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun _ _ args st iargs pre => hm args st iargs pre _

/-- **A ghost-fixed function's spec from its unrolled tree**: `holdsFn_of_tree_fixed` for
`eraseFnL`. -/
theorem holdsFn_of_tree_fixedL {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {fn : Fn} {f : Source.FunctionDef}
    (hsel : fn.sel < 2 ^ 32) (hfind : c.core.findFunctionBySelector? fn.sel = some f)
    (hlen : f.params.length = fn.params.length) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel f = some T) {b : Bundle} {fs : FnSpec}
    {ctxOf : Call → Ctx} {step : GhostStep} {ctx : Ctx}
    (hctx : ∀ call : Call, call.callvalue = 0 → ctxOf call = ctx)
    (hstep : ∀ call, SolidCore.Verify.VC.stageScope fn s call → ∀ g, step call g = g)
    (hm : TreeMeetsFixed b fs ctx fn.params.length T) :
    HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs :=
  holdsFn_of_tree_run (fun _ hcov args hl hargs =>
    source_runL hd hcov hsel hfind hT args (hl.trans hlen.symm) hargs) hctx
    fun call hcall args st iargs pre => by
      rw [hstep call hcall pre.ghost]; exact hm args st iargs pre

end SolidCore.Spec

namespace SolidCore.Refinement.Shapes
open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Spec

/-- SolidCore rejects a value on every call of a function `checkL` and the value check accept:
`run_value` from `checkL`. -/
theorem run_valueL {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.checkL fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true) {g : Fn} (hg : g ∈ fns)
    (args : List Nat) (hlen : args.length = g.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    {v : Nat} (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    (solidCore fuel).run c { calldata := calldata g.sel args, callvalue := v, storage := σ } =
      some (rejected σ) := by
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := Generic.checkL_mem hchk hg
  obtain ⟨hpay, -⟩ := Generic.checkValue_mem hval hg hfind
  obtain ⟨ws, hw⟩ := Generic.eraseFnL_widths ht1
  exact Generic.source_run_value hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ

/-- **One function spec on the stage's calls at every value**, `holdsFn_genericValid` from
`checkL`. -/
theorem holdsFn_genericValidL {fuel mirFuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {d : SolidCore.Solidity.Source.State} {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s)
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.checkL fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep} {fs : FnSpec}
    (hctx : ∀ call, (ctxOf call).value = call.callvalue)
    (hguard : fs.succeedsIf = [] ∨ valueGuarded fs)
    {fn : Fn} (hfn : fn.sel = fs.selector) (hok : selOk fns fn.sel fn.params.length = true)
    (h : HoldsFn (solidCore fuel) c (SolidCore.Verify.VC.stageScope fn s) b ctxOf step fs) :
    HoldsFn (solidCore fuel) c (genericValid fns s) b ctxOf step fs := by
  rintro _ ⟨σ, v, hcov, hv, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  by_cases hv0 : v = 0
  · subst hv0
    exact holdsFn_genericValid0 hfn hok h _ ⟨σ, hcov, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  · refine ⟨_, run_valueL hd hchk hval hg args hlen hargs hv0 hv σ, fun hs => absurd hs (by
      simp [rejected]), fun hne hsat => absurd hsat (not_sat_of_value (hguard.resolve_left hne) ?_)⟩
    simp only [SolidCore.Spec.mkEnv, hctx]
    exact_mod_cast hv0

end SolidCore.Refinement.Shapes

/-- info: 'SolidCore.Spec.holdsFn_of_treeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Spec.holdsFn_of_treeL

/-- info: 'SolidCore.Refinement.Shapes.holdsFn_genericValidL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.holdsFn_genericValidL
