import Verify.Generic.Expected
import Verify.Generic.CtorWords
import Verify.ShapeSpecExport

/-!
# The certified tier for a constructor with word arguments

The pieces that carry a spec connection over every constructor argument list
(Verify/Spec/TreeArgs.lean, `spec_connect.py --ctor-args`) into the published statement
`Generic.Expected (src.withArgs ws)`, as `Shapes.compiledArgs` (CtorWords.lean) carries the compiled tier:

* `run_value_args` and `holdsFn_genericValidArgs`: `Shapes.run_value` and `Shapes.holdsFn_genericValid`
  for the contract deployed with the words `ws` (`solidCoreFromArgs callerAddress fuel ws`): a call with a
  value of a function the value check accepts reverts with empty data, so a function spec's `HoldsFn`
  on the stage's calls of its function gives it on the stage's valid calls at every value.
* `certifiedArgs`: `Shapes.Certified` of that semantics with solar-verify's exported postcondition and
  allowed statuses, from `compiledArgs`'s `Compiled` and the spec's `Holds`.
* `certifiedAt_defaultArgs`: `Generic.certifiedAt_default` for that semantics, the obligation of
  `Expected (src.withArgs ws)` in the default context.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Spec (Bundle FnSpec Pre Post HoldsFn Holds)

/-- SolidCore rejects a value on every call of a function the generic check and the value check
accept, against the contract deployed with the argument words `ws`. -/
theorem run_value_args {fuel mirFuel : Nat} {ws : List Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    (hd : Generic.Loop.LoadDeployed fuel c ws d)
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true) {g : Fn} (hg : g ∈ fns)
    (args : List Nat) (hlen : args.length = g.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    {v : Nat} (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    (solidCoreFromArgs callerAddress fuel ws).run c
        { calldata := calldata g.sel args, callvalue := v, storage := σ } = some (rejected σ) := by
  have hcf := List.all_eq_true.mp hchk g hg
  have hcv := List.all_eq_true.mp hval g hg
  unfold Generic.checkFn at hcf
  unfold Generic.checkValueFn at hcv
  cases hfind : c.core.findFunctionBySelector? g.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : Generic.eraseFn (Generic.envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  simp only [hfind, ht1, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  simp only [hfind, Bool.and_eq_true, Bool.not_eq_true'] at hcv
  obtain ⟨wds, hw⟩ := Generic.eraseFn_widths ht1
  exact Generic.source_run_value_args hd hsel hfind hw hcv.1 args (by rw [hlen, hpl]) hargs hv0 hv σ

/-- **One function spec on the stage's valid calls at every value**, for the contract deployed with
the argument words `ws`: `holdsFn_genericValid` for `solidCoreFromArgs callerAddress fuel ws`. -/
theorem holdsFn_genericValidArgs {fuel mirFuel : Nat} {ws : List Nat}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {d : SolidCore.Solidity.Source.State}
    (hd : Generic.Loop.LoadDeployed fuel c ws d) {s : List (Nat × Nat)}
    {m : SolarTV.MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {b : Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep} {fs : FnSpec}
    (hctx : ∀ call, (ctxOf call).value = call.callvalue)
    (hguard : fs.succeedsIf = [] ∨ valueGuarded fs)
    {fn : Fn} (hfn : fn.sel = fs.selector) (hok : selOk fns fn.sel fn.params.length = true)
    (h : HoldsFn (solidCoreFromArgs callerAddress fuel ws) c (SolidCore.Verify.VC.stageScope fn s) b
      ctxOf step fs) :
    HoldsFn (solidCoreFromArgs callerAddress fuel ws) c (genericValid fns s) b ctxOf step fs := by
  rintro _ ⟨σ, v, hcov, hv, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  by_cases hv0 : v = 0
  · subst hv0
    exact holdsFn_genericValid0 hfn hok h _ ⟨σ, hcov, g, hg, args, hlen, hargs, rfl⟩ iargs pre hpre
  · refine ⟨_, run_value_args hd hchk hval hg args hlen hargs hv0 hv σ, fun hs => absurd hs (by
      simp [rejected]), fun hne hsat => absurd hsat (not_sat_of_value (hguard.resolve_left hne) ?_)⟩
    simp only [SolidCore.Spec.mkEnv, hctx]
    exact_mod_cast hv0

/-- **`Shapes.Certified` for the contract deployed with the argument words `ws`**: `compiledArgs`'s
`Compiled` on the stage's valid calls, with solar-verify's exported postcondition and allowed statuses,
from the spec's `Holds` there (each function's from `holdsFn_genericValidArgs`). -/
theorem certifiedArgs {fuel : Nat} {ws : List Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {fns : List Fn} {s : List (Nat × Nat)} {G : Call → Nat} {b : Bundle}
    {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep}
    (h : Compiled (solidCoreFromArgs callerAddress fuel ws) c code (genericValid fns s) G)
    (hh : Holds (solidCoreFromArgs callerAddress fuel ws) c (genericValid fns s) b ctxOf step) :
    Certified (solidCoreFromArgs callerAddress fuel ws) c code (genericValid fns s)
      (bundleAllowed b ctxOf) (bundlePost b ctxOf step) G :=
  h.certified_of_holds (fun _ h => h) hh

/-- info: 'SolidCore.Refinement.Shapes.holdsFn_genericValidArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holdsFn_genericValidArgs

/-- info: 'SolidCore.Refinement.Shapes.certifiedArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedArgs

end SolidCore.Refinement.Shapes

namespace SolidCore.Verify.Generic

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Solidity

/-- **`certifiedAt_default` for the contract deployed with the argument words `ws`**: a
`Shapes.Certified` statement of `solidCoreFromArgs callerAddress fuel ws` is `CertifiedAt` the default
context, the obligation of `Expected (src.withArgs ws)` there (`Source.semAt_withArgs`). -/
theorem certifiedAt_defaultArgs {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract}
    {code : ByteArray} {Valid : Call → Prop} {Allowed Post : Call → Observable → Prop}
    {G : Call → Nat} (h : Certified (solidCoreFromArgs callerAddress fuel ws) c code Valid Allowed Post G) :
    CertifiedAt (solidCoreFromArgs Context.default.caller fuel ws) c Context.default code Valid Allowed
      Post G where
  translation :=
    { inhabited := h.inhabited
      equiv := by
        intro gas hg call hc obs hrun
        rw [runAt_default] at hrun
        exact h.equiv gas hg call hc obs hrun
      terminates := fun call hc => by
        obtain ⟨obs, hs, -⟩ := h.terminates call hc
        exact ⟨obs, hs, trivial⟩
      resources := fun call hc => by
        obtain ⟨hG, hr⟩ := h.resources call hc
        exact ⟨hG, fun gas h1 h2 => by rw [runAt_default]; exact hr gas h1 h2⟩ }
  spec :=
    { allowed := fun call hc obs hs => by
        obtain ⟨obs', hs', ha⟩ := h.terminates call hc
        have e : (solidCoreFromArgs callerAddress fuel ws).run c call = some obs := hs
        rw [e] at hs'; cases hs'; exact ha
      meets := h.meets }

/-- info: 'SolidCore.Verify.Generic.certifiedAt_defaultArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedAt_defaultArgs

end SolidCore.Verify.Generic
