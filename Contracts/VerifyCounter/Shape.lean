import Verify.ShapeGeneric
import Contracts.VerifyCounter.Total
import Contracts.VerifyCounter.Holds

/-!
# VerifyCounter's bump: equivalence, termination and the specification, in the published shape

The source of this statement is solar's first lowered MIR `stage0` of solar-verify's Counter
(crates/verify/examples/Counter.sol), under the oracle with EthLib's caller, Keccak-256 and
environment (`Shapes.oracle`): no SolidCore stage reaches loops yet, so the frontend trust
boundary is at the first lowered MIR. On every call of `bump(uint256)` (`IsBump`: its selector):

* equivalence: every result of the exact bytecode at every gas is `stage0`'s, or a failure that
  changes nothing (`Bump.bump_total`: the loop checker on the final EVM IR, cut-point stages read
  backwards);
* termination: `stage0` ends within `(n + 2) * 40` blocks, by the ranking certificate the kernel
  checks (`Bump.stage0_ends_within`, termination's `CutPoint.ends_within_start` on generated
  invariants, `Contracts/VerifyCounter/Inferred.lean`);
* the specification: solar-verify's `VerifyCounter.spec` of every result (`holds_stage0`).

Resources are not proved: the cut-point stages give the final EVM IR's end, not a block count, so
`AssembleLoop.forward_of_checkL` has no bound to start from. This is `Shapes.Functional`, never the
strongest status.
-/

namespace Contracts.VerifyCounter.Shape

open SolidCore.Refinement SolarTV.Milestone.VerifyCounter.Bump

/-- A call of `bump(uint256)` exists: its selector on one zero word. -/
theorem inhabited : ∃ call, IsBump call :=
  ⟨{ calldata := Abi.calldata 0xb20eb4c4 [0], callvalue := 0, storage := [] }, by
    unfold IsBump; decide +kernel⟩

/-- **What the published statement asks of this module.** -/
theorem published :
    Shapes.Functional (SolarTV.mirSem Shapes.oracle) SolarTV.Export.Counter.stage0
      SolarTV.Milestone.VerifyCounter.code IsBump (fun _ _ => True)
      (Shapes.specPost SolidCore.Refinement.Solar.VerifyCounter.spec) :=
  Shapes.functional_of inhabited
    (fun call h => (bump_total Shapes.oracle (fun _ => Shapes.oracle_ok.1) (fun _ => Shapes.oracle_ok.2)
      call h).2.2.1)
    (fun _ _ _ _ => trivial)
    (fun gas call h obs hrun => (bump_total Shapes.oracle (fun _ => Shapes.oracle_ok.1)
      (fun _ => Shapes.oracle_ok.2) call h).2.2.2 gas call rfl obs hrun)
    (Shapes.meets_of_holds (SolidCore.Refinement.Solar.VerifyCounter.Mir.holds_stage0 Shapes.oracle))

/-- info: 'Contracts.VerifyCounter.Shape.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

end Contracts.VerifyCounter.Shape
