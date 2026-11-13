import SolidCore.Spec.TrustedBase.Hypotheses
import SolidCore.Refinement.Source.C4
import SolidCore.Refinement.Solar.Counter.Source

/-!
# The trusted base for c4 and Counter

c4 (`scripts/refinement/corpus/c4.sol`, the source of the spec corpus's `c4.sol`) and Counter
(`scripts/refinement/counter/counter.sol`) have no inline assembly, no `@custom:assume`, no
`@custom:trusted` function and no `Math.mulDiv`, hash nothing and call nothing. Their trusted base:

* inline assembly: `AsmFree` of the source units SolidCore checks, by the kernel (`asmFree_c4`,
  `asmFree_counter`);
* assume, trusted, `Math.mulDiv`: none to assume (`Hyps.plain`);
* keccak256 and external calls: given that a call hashes nothing and makes no external call, every
  hypothesis holds (`c4_on`, `counter_on`). That premise is not yet proved of SolidCore's run:
  its interpreter hashes internally and `Source.run` folds its interaction tree without exposing
  the transcript. For c4 the spec is in any case proved in Lean of SolidCore and of the bytecode
  (`SolidCore.Spec.Solar.C4.holds_bytecode`), without the trusted base.
-/

namespace SolidCore.Spec.TrustedBase.Instances

open SolarTV SolidCore.Spec SolidCore.Spec.TrustedBase

/-- c4's source has no inline assembly. -/
theorem asmFree_c4 : AsmFree SolidCore.Refinement.Source.C4.importedSourceUnit := by decide

/-- Counter's source has no inline assembly. -/
theorem asmFree_counter : AsmFree SolidCore.Refinement.Source.Counter.importedSourceUnit := by
  decide

/-- **c4's trusted base, discharged** on every call, for any source semantics and program: no
hashing, no external call (the empty transcript), its assembly-free source. -/
theorem c4_on (S : Sem) (p : S.Prog) (deployed : Nat → Nat) (scope : Call → Prop) (b : Bundle)
    (ctxOf : Call → Ctx) (step : GhostStep) (call : Call) :
    ((Hyps.plain S p SolidCore.Refinement.Source.C4.importedSourceUnit deployed
      (fun _ => [])).toAssumptions scope b ctxOf step).On call :=
  Hyps.plain_on asmFree_c4 (fun _ => Hyps.defaultCalls_nil) scope b ctxOf step call

/-- **Counter's trusted base, discharged**, as c4's. -/
theorem counter_on (S : Sem) (p : S.Prog) (deployed : Nat → Nat) (scope : Call → Prop)
    (b : Bundle) (ctxOf : Call → Ctx) (step : GhostStep) (call : Call) :
    ((Hyps.plain S p SolidCore.Refinement.Source.Counter.importedSourceUnit deployed
      (fun _ => [])).toAssumptions scope b ctxOf step).On call :=
  Hyps.plain_on asmFree_counter (fun _ => Hyps.defaultCalls_nil) scope b ctxOf step call

/-- **The spec of the bytecode from solar-verify's verdict on Counter, with the trusted base
discharged**: the verdict and a stage give the spec on the whole scope. -/
theorem counter_spec_of_verdict {S T : Sem} {p : S.Prog} {q : T.Prog} {scope : Call → Prop}
    {b : Bundle} {ctxOf : Call → Ctx} {step : GhostStep} (deployed : Nat → Nat)
    (hwf : b.WF = true) (hopaque : OpaqueInRange b)
    (verdict : Verdict S p scope b ctxOf step
      ((Hyps.plain S p SolidCore.Refinement.Source.Counter.importedSourceUnit deployed
        (fun _ => [])).toAssumptions scope b ctxOf step))
    (stage : Stage S T p q scope) : Holds T q scope b ctxOf step :=
  fun fs hfs => (spec_of_verdict_hyps _ hwf hopaque verdict stage fs hfs).mono fun call h =>
    ⟨h, counter_on S p deployed scope b ctxOf step call⟩

end SolidCore.Spec.TrustedBase.Instances
