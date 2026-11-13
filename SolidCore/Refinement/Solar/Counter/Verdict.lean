import SolidCore.Refinement.Solar.Counter.Final
import SolidCore.Spec.TrustedBase.Instances

/-!
# The counter milestone's bytecode meets solar-verify's spec, given its verdict

This is where the certified translation and solar-verify meet for the counter milestone
(solar-tv/milestone/counter, the source `scripts/refinement/counter/counter.sol`). The stage from
SolidCore's checked contract to solar's bytecode is a theorem (`agree`, from
`Counter.Every`'s source run and `Counter.Final.target_every`, which compose solar-tv's backend
stages); the bytecode is bound to the exporter's manifest (`Counter.Final.bound`: its hex and
SHA-256, checked by the kernel) and runs in one frame (`Counter.Final.frameLocal`).

`bytecode_spec_of_verdict` takes the rest as hypotheses and nothing else: a spec bundle `b`
(what `solar-verify --emit-lean-spec` exports), its well-formedness and opaque ranges, and
solar-verify's verdict on SolidCore's contract under the trusted base `Hyps.plain` of
`SolidCore.Spec.TrustedBase` (no hashing, no external call, no assembly, no assume, no trusted
function), which `TrustedBase.Instances.counter_on` discharges. The verdict is the only premise
about the spec: the theorem holds for every bundle whose verdict holds, and for a bundle the
bytecode does not meet the conclusion fails, so the verdict fails too.

What it covers: runtime calls of `scopeEvery` (`inc` and `get` with any value, malformed call
data and unknown selectors, from any storage), under EthLib's run at its default gas limit
(`Target.run`). Not covered: deployment, other gas limits, and calls from other contracts
(the code makes none).
-/

namespace SolidCore.Refinement.Solar.Counter.Verdict

open SolidCore.Refinement SolidCore.Refinement.Final

/-- The counter's trusted base: nothing to trust beyond the verdict (`Hyps.plain`). -/
abbrev hyps (c : SolidCore.Solidity.TypeCheck.CheckedContract) (deployed : Nat → Nat) :
    SolidCore.Spec.TrustedBase.Hyps (solidCore fuel) c :=
  SolidCore.Spec.TrustedBase.Hyps.plain (solidCore fuel) c Source.Counter.importedSourceUnit
    deployed (fun _ => [])

/-- SolidCore's checked counter and solar's bytecode show the same observable on every call of
the scope. -/
theorem agree {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Agree (solidCore fuel) ethLib c code scopeEvery :=
  fun call h => ⟨_, source_run_every hc call h, Final.target_every call h⟩

/-- **The counter's bytecode meets every spec solar-verify accepts of its source.** -/
theorem bytecode_spec_of_verdict {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    {b : SolidCore.Spec.Bundle} {ctxOf : Call → SolidCore.Spec.Ctx}
    {step : SolidCore.Spec.GhostStep} (deployed : Nat → Nat)
    (hwf : b.WF = true) (hopaque : SolidCore.Spec.OpaqueInRange b)
    (verdict : SolidCore.Spec.Verdict (solidCore fuel) c scopeEvery b ctxOf step
      ((hyps c deployed).toAssumptions scopeEvery b ctxOf step)) :
    Bound Final.manifest code ∧ FrameLocal code = true ∧
      Agree (solidCore fuel) ethLib c code scopeEvery ∧
      SolidCore.Spec.Holds ethLib code scopeEvery b ctxOf step :=
  ⟨Final.bound, Final.frameLocal, agree hc,
    SolidCore.Spec.TrustedBase.Instances.counter_spec_of_verdict deployed hwf hopaque verdict
      (agree hc).stage⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.Verdict.bytecode_spec_of_verdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode_spec_of_verdict

end SolidCore.Refinement.Solar.Counter.Verdict
