import Contracts.VerifyCounter.BumpTotal
import verify_counter.Proofs.Execution
import verify_counter.Proofs.Stages

/-!
# bump: termination, spec and the exact bytecode in one statement

`bump_total` puts together, for every call of `bump(n)` and every oracle the assembly
certificate admits:

* termination with a bound from the ranking certificate: the first lowered MIR ends within
  `(n + 2) * 40` blocks (`Bump.stage0_ends_within`, the generic checker
  `CutPoint.ends_within_start`), in an end meeting bump's spec `Post`;
* the final EVM IR ends too, in an end meeting `Post`, through the backend stages read forwards
  (`verify_counter_certified`, cut-point simulations, so the loop's iterations correspond);
* the exact bytecode, at every gas: each of its results is the MIR's, which exists, or a failure
  that leaves storage and logs as they were (`verify_counter_bytecode`, `checkL`).

What it does not say: that some gas makes the bytecode succeed. Running out of gas is the failure
branch of the last conjunct; a proved gas bound needs a forward per-block gas lemma of the
assembly checker, which no checker has yet (see `CutPoint.gas_ends` for the composition it would
feed).
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1

theorem bump_total (o : Oracle)
    (ho : cert.env = true → SolidCore.Refinement.Solar.Assemble.OracleOk o)
    (he : cert.reads = true → SolidCore.Refinement.Solar.Assemble.EnvOk o)
    (call : Call) (hsel : IsBump call) :
    (∃ r, Machine.iterate (MIR.Lowered.moduleBlock o call stage0)
        (((calldataWord call 4).toNat + 2) * 40) (start call) = some r ∧ Post call r) ∧
    (∃ r, EVM.Program.layer.Ends o evm11 call r ∧ Post call r) ∧
    ((mirSem o).run stage0 call).isSome ∧
    ∀ gas, SolidCore.Refinement.Final.Within (mirSem o) (SolidCore.Refinement.Final.ethLibWith gas)
      stage0 code (· = call) := by
  obtain ⟨r, ran, post⟩ := stage0_ends_within o call hsel
  refine ⟨⟨r, ran, post⟩, ends_of_certified o (verify_counter_certified o) call hsel, ?_, fun gas => by
    intro c _ obs h
    exact verify_counter_bytecode o ho he gas c (show anyCall c from trivial) obs h⟩
  have e : MIR.Lowered.moduleLayer.Ends o stage0 call r :=
    ⟨_, by change Machine.iterate _ _ _ = some r; exact ran⟩
  change ((MIR.Lowered.moduleLayer.result o stage0 call).map _).isSome = true
  rw [MIR.Lowered.moduleLayer.result_of_ends e]
  rfl

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.bump_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bump_total

end SolarTV.Milestone.VerifyCounter.Bump
