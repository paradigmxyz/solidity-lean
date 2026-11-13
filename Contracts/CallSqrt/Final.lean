import Contracts.CallSqrt.Total
import callsqrt.Proofs.Execution

/-!
# CallSqrt: termination and the exact bytecode in one statement

For every call of CallSqrt (any calldata, call value and storage) and every oracle the assembly
certificate admits:

* the first lowered MIR ends (`stage0_ends`: Math.sqrt's Newton loop by its generated ranking
  certificate `z`, under either caller);
* the final EVM IR ends, through the backend stages read forwards (`callsqrt_certified`, cut-point
  simulations), in an end that agrees with the MIR's;
* every result of the exact bytecode, at every gas, is the MIR's (which exists) or a failure that
  leaves storage and logs as they were (`callsqrt_bytecode`, `checkL`).

Not stated: that some gas makes the bytecode succeed. Running out of gas is the failure branch of
the last conjunct; a proved gas bound needs a forward per-block gas lemma of the assembly checker.
No user spec of sqrt is stated here: its spec (`z * z <= y < (z + 1) * (z + 1)`) is solar-verify's
SMT result, not yet connected to these semantics.
-/

namespace SolarTV.Milestone.CallSqrt

open Machine SolarTV.Export.CallSqrt SolarTV.Milestone.W1

theorem callsqrt_total (o : Oracle)
    (ho : Callsqrt.cert.env = true → SolidCore.Refinement.Solar.Assemble.OracleOk o)
    (he : Callsqrt.cert.reads = true → SolidCore.Refinement.Solar.Assemble.EnvOk o) (call : Call) :
    (∃ r, MIR.Lowered.moduleLayer.Ends o stage0 call r) ∧
    (∃ r, EVM.Program.layer.Ends o evm13 call r) ∧
    ((mirSem o).run stage0 call).isSome ∧
    ∀ gas, SolidCore.Refinement.Final.Within (mirSem o) (SolidCore.Refinement.Final.ethLibWith gas)
      stage0 Callsqrt.code (· = call) := by
  obtain ⟨r, e⟩ := stage0_ends o call
  obtain ⟨r', e', -⟩ := Callsqrt.callsqrt_certified o call trivial r e
  refine ⟨⟨r, e⟩, ⟨r', e'⟩, ?_, fun gas => by
    intro c _ obs h
    exact Callsqrt.callsqrt_bytecode o ho he gas c (show anyCall c from trivial) obs h⟩
  change ((MIR.Lowered.moduleLayer.result o stage0 call).map _).isSome = true
  rw [MIR.Lowered.moduleLayer.result_of_ends e]
  rfl

/-- info: 'SolarTV.Milestone.CallSqrt.callsqrt_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callsqrt_total

end SolarTV.Milestone.CallSqrt
