import Verify.ShapeGeneric
import Verify.Spec.Contract
import SolidCore.Refinement.Solar.AssembleCtxCall

/-!
# The functional shape of a generic-stage contract through the context checker

For a contract whose bytecode only the checker with calling contexts and STATICCALL accepts
(`AssembleCtx.checkXB`, the runtime of a token with `ecrecover`, whose internal functions are
called from several places), and on the calls of the functions the generic source stage accepts,
`functional_ctx` composes:

* the generic source stage (`Generic.check` on the first lowered MIR, under every oracle whose
  caller and Keccak-256 are EthLib's),
* solar-tv's backend stages from that MIR to the final EVM IR, under every oracle, on a scope
  covering the valid calls,
* the context checker's per-run theorem: at every gas below `2 ^ 256`, each valid call has an
  oracle meeting the certificate's `CertOk` under which every result of the exact bytecode is the
  final EVM IR's, or a failure that changes nothing,
* a specification of SolidCore's runs on the valid calls (`Meets`),

into `Shapes.Functional`: equivalence (gas-insensitive), termination (`Generic.definedAt`) and the
specification. It does not give `Resources`: the context checker proves no gas bound, so a
contract certified through this theorem never reaches `Shapes.Certified` from it alone.

`meets_of_holdsFn` turns a solar-verify function spec proved of SolidCore's contract
(`SolidCore.Spec.HoldsFn`) into the postcondition `holdsPost` of every source result.
-/

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar SolidCore.Solidity

/-- An oracle whose caller and Keccak-256 are EthLib's is one every generic source stage takes. -/
theorem sourceEnvOk_of {o : Machine.Oracle} (h : Assemble.OracleOk o) : Generic.SourceEnvOk o :=
  ⟨by unfold Generic.CallerOk; rw [h.1]; exact callerAddress_word,
    fun a b _ _ => by rw [h.2]; exact Keccak.ethKeccak_twoWords a b⟩

/-- **The functional shape through the context checker.** -/
theorem functional_ctx {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {base : Assemble.Cert}
    (henv : base.env = true)
    (inhabited : ∃ call, genericValid0 fns s call)
    (backend : ∀ o, Stage (mirSem o) (evmirSem o) m q scope)
    (hscope : ∀ call, genericValid0 fns s call → scope call)
    (asm : ∀ gas, gas < 2 ^ 256 → ∀ call, genericValid0 fns s call → ∃ o,
      RunOracle.CertOk base o ∧ Within (evmirSem o) (ethLibWith gas) q code (· = call))
    {Post : Call → Observable → Prop} (meets : Meets (solidCore fuel) c (genericValid0 fns s) Post) :
    Functional (solidCore fuel) c code (genericValid0 fns s) (fun _ _ => True) Post := by
  have defined := Generic.definedAt hd hchk
  have total : ∀ call, genericValid0 fns s call → ∃ obs, (solidCore fuel).run c call = some obs :=
    fun call hc => Option.isSome_iff_exists.mp (defined call hc)
  refine ⟨inhabited, ?_, fun call hc => ?_, meets⟩
  · exact equiv_of_runs (sem := evmirSem) (q := fun _ => q) (Ok := RunOracle.CertOk base) total
      (fun o ho => (Generic.stageAtWith o hd (sourceEnvOk_of (ho.1 henv)).ask hchk).trans
        ((backend o).mono hscope))
      asm
  · obtain ⟨obs, hs⟩ := total call hc
    exact ⟨obs, hs, trivial⟩

/-- A solar-verify function spec as a postcondition: on a call of `scope`, every pre-state and
arguments meeting the spec's precondition meet its postcondition with the call's result. -/
def holdsPost (b : SolidCore.Spec.Bundle) (ctxOf : Call → SolidCore.Spec.Ctx)
    (step : SolidCore.Spec.GhostStep) (fs : SolidCore.Spec.FnSpec) (scope : Call → Prop)
    (call : Call) (obs : Observable) : Prop :=
  scope call → ∀ (args : List Int) (pre : SolidCore.Spec.State),
    SolidCore.Spec.Pre b fs (ctxOf call) pre call args →
      SolidCore.Spec.Post b fs (ctxOf call) pre (step call pre.ghost) obs args

/-- A function spec proved of the source is `Meets` of its `holdsPost`. -/
theorem meets_of_holdsFn {S : Sem} {p : S.Prog} {Valid scope : Call → Prop}
    {b : SolidCore.Spec.Bundle} {ctxOf : Call → SolidCore.Spec.Ctx} {step : SolidCore.Spec.GhostStep}
    {fs : SolidCore.Spec.FnSpec} (h : SolidCore.Spec.HoldsFn S p scope b ctxOf step fs) :
    Meets S p Valid (holdsPost b ctxOf step fs scope) := by
  intro call _ obs hrun hs args pre hpre
  obtain ⟨obs', hrun', hpost⟩ := h call hs args pre hpre
  rw [hrun] at hrun'
  cases hrun'
  exact hpost

/-- info: 'SolidCore.Refinement.Shapes.functional_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms functional_ctx

/-- info: 'SolidCore.Refinement.Shapes.meets_of_holdsFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meets_of_holdsFn

end SolidCore.Refinement.Shapes
