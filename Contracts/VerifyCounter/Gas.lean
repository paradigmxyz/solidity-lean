import Contracts.VerifyCounter.EvmBound
import Contracts.VerifyCounter.Total
import SolidCore.Refinement.Solar.AssembleGasLoop

/-!
# bump: a proved gas bound on the exact bytecode

From the loop's rank to gas, all four pieces checked:

* the MIR's ranking certificate (`n - i`, inferred) and the stages' stated segment fuel give a
  block bound on the final EVM IR: every call of bump ends on `evm11` within `(n + 2) * 22`
  blocks (`evm11_ends_within`);
* the assembly checker run forward (`AssembleLoop.forward_of_checkL`) turns a block bound into
  gas: from `gasBoundL cert N = 22100 * (N * bmax cert) + memoryGasCost cert.top` on, the bytecode
  shows exactly the EVM IR's result, reverts included.

So at every gas from `G call = gasBoundL cert ((n + 2) * 22)` the exact bytecode runs `bump(n)`
to the observable of an end that meets bump's spec `Post` (`bump_gas`): it does not run out of
gas, and what it shows is the end the MIR's spec speaks of. The bound is linear in `n`, as the loop
is. Scope: the counter's bytecode reads no `GAS` and makes no call, so EIP-150 forwarding and
gas-dependent callees do not arise here; the oracle premises are the assembly certificate's
(`cert.env`, `cert.reads`).
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1 SolarTV.Milestone.VerifyCounter

/-- The gas bump's bytecode needs on a call with argument `n`. -/
def gasBound (call : Call) : Nat :=
  SolidCore.Refinement.Solar.AssembleLoop.gasBoundL cert (((calldataWord call 4).toNat + 2) * 22)

/-- **bump's bytecode does not run out of gas from `gasBound call` on, and meets its spec.** -/
theorem bump_gas (o : Oracle)
    (ho : cert.env = true → SolidCore.Refinement.Solar.Assemble.OracleOk o)
    (he : cert.reads = true → SolidCore.Refinement.Solar.Assemble.EnvOk o)
    (call : Call) (hsel : IsBump call) {gas : Nat} (hg : gasBound call ≤ gas) :
    ∃ r, SolidCore.Refinement.Final.Target.runWith gas code call = some (observe call r.2 r.1) ∧
      Post call r := by
  obtain ⟨r, hit⟩ := evm11_ends_within o call hsel
  refine ⟨r, SolidCore.Refinement.Solar.AssembleLoop.forward_of_checkL check_ok o ho he call _ r hit hg,
    ?_⟩
  obtain ⟨-, ⟨r', e', post⟩, -⟩ := bump_total o ho he call hsel
  have e : EVM.Program.layer.Ends o evm11 call r := ⟨((calldataWord call 4).toNat + 2) * 22, hit⟩
  rw [EVM.Program.layer.ends_unique e e']
  exact post

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.bump_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bump_gas

end SolarTV.Milestone.VerifyCounter.Bump
