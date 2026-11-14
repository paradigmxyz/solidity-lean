import Verify.ShapeGeneric
import Contracts.VerifyCounter.Gas
import Contracts.VerifyCounter.Holds
import Contracts.VerifyCounter.ShapeSpec

/-!
# VerifyCounter's bump: all four obligations, in the published shape

The source of this statement is solar's first lowered MIR `stage0` of solar-verify's Counter
(crates/verify/examples/Counter.sol), under the oracle with EthLib's caller, Keccak-256 and
environment (`Shapes.oracle`). No SolidCore stage reaches loops yet, so the frontend trust boundary
is at the first lowered MIR. On every call of `bump(uint256)` (`IsBump`: its selector):

* equivalence: every result of the exact bytecode at every gas is `stage0`'s, or a failure that
  changes nothing (`Bump.bump_total`: the loop checker on the final EVM IR, cut-point stages read
  backwards);
* termination: `stage0` ends within `(n + 2) * 40` blocks, by the ranking certificate the kernel
  checks (`Bump.stage0_ends_within` on generated invariants, `Contracts/VerifyCounter/Inferred.lean`);
* the specification: solar-verify's `VerifyCounter.spec` of every result (`holds_stage0`).

That is `functional`, on every argument. Resources (`resources`): the final EVM IR ends within
`(n + 2) * 22` blocks (`Bump.evm11_ends_within`: the rank carried along the bounded stage
simulations), so from `Bump.gasBound call = gasBoundL cert ((n + 2) * 22)` gas on the bytecode
gives exactly `stage0`'s result (`AssembleLoop.stage_of_checkL_gas` after the forward stages). The
bound grows with `n`; `Shapes.Resources` asks for a bound below `2 ^ 64`, so the published
statement (`published`, `Shapes.Certified`) declares the valid calls `ValidB`: bump with
`n < 2 ^ 32`, where the bound is below `2 ^ 64` (`gasBound_lt`).
-/

namespace Contracts.VerifyCounter.Shape

open SolidCore.Refinement SolarTV.Milestone.VerifyCounter.Bump Contracts.VerifyCounter.ShapeSpec

/-- A call of `bump(uint256)` exists: its selector on one zero word. -/
theorem inhabited : ∃ call, IsBump call :=
  ⟨{ calldata := Abi.calldata 0xb20eb4c4 [0], callvalue := 0, storage := [] }, by
    unfold IsBump; decide +kernel⟩

/-- Equivalence, termination and the specification on every call of `bump`. -/
theorem functional :
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

theorem inhabitedB : ∃ call, ValidB call :=
  ⟨{ calldata := Abi.calldata 0xb20eb4c4 [0], callvalue := 0, storage := [] }, by
    unfold ValidB IsBump; decide +kernel⟩

/-- On those calls the gas bound is below `2 ^ 64`. -/
theorem gasBound_lt (call : SolarTV.Call) (h : (SolarTV.Machine.calldataWord call 4).toNat < 2 ^ 32) :
    gasBound call < 2 ^ 64 := by
  have hn : ((SolarTV.Machine.calldataWord call 4).toNat + 2) * 22 ≤ (2 ^ 32 + 2) * 22 :=
    Nat.mul_le_mul_right _ (by omega)
  have hm : gasBound call ≤
      Solar.AssembleLoop.gasBoundL SolarTV.Milestone.VerifyCounter.cert ((2 ^ 32 + 2) * 22) := by
    unfold gasBound Solar.AssembleLoop.gasBoundL
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 22100 (Nat.mul_le_mul_right _ hn)) _
  have hc : Solar.AssembleLoop.gasBoundL SolarTV.Milestone.VerifyCounter.cert ((2 ^ 32 + 2) * 22) <
      2 ^ 64 := by
    decide +kernel
  exact Nat.lt_of_le_of_lt hm hc

/-- **Resources**: from `gasBound call` on, the exact bytecode gives `stage0`'s result. -/
theorem resources :
    Shapes.Resources (SolarTV.mirSem Shapes.oracle) SolarTV.Export.Counter.stage0
      SolarTV.Milestone.VerifyCounter.code ValidB gasBound :=
  Shapes.resources_of_forward (B := SolarTV.evmirSem Shapes.oracle) (q := SolarTV.Export.Counter.evm11)
    (fun call h => Option.isSome_iff_exists.mp
      (bump_total Shapes.oracle (fun _ => Shapes.oracle_ok.1) (fun _ => Shapes.oracle_ok.2) call h.1).2.2.1)
    ((SolarTV.Milestone.VerifyCounter.verify_counter_mir_to_evmir Shapes.oracle).mono fun _ _ => trivial)
    (fun call h => ⟨gasBound_lt call h.2, fun _ h1 _ obs hrun =>
      Solar.AssembleLoop.stage_of_checkL_gas SolarTV.Milestone.VerifyCounter.check_ok Shapes.oracle
        (fun _ => Shapes.oracle_ok.1) (fun _ => Shapes.oracle_ok.2) call _
        (evm11_ends_within Shapes.oracle call h.1) h1 obs hrun⟩)

/-- **What the published statement asks of this module**: all four obligations. -/
theorem published :
    Shapes.Certified (SolarTV.mirSem Shapes.oracle) SolarTV.Export.Counter.stage0
      SolarTV.Milestone.VerifyCounter.code ValidB (fun _ _ => True)
      (Shapes.specPost SolidCore.Refinement.Solar.VerifyCounter.spec) gasBound :=
  ⟨inhabitedB, fun gas hg call h => functional.equiv gas hg call h.1,
    fun call h => functional.terminates call h.1, fun call h => functional.meets call h.1, resources⟩

/-- info: 'Contracts.VerifyCounter.Shape.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms functional

/-- info: 'Contracts.VerifyCounter.Shape.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

end Contracts.VerifyCounter.Shape
