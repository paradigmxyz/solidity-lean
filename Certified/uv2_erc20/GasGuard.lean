import W1Proofs.Tactic
import W1Proofs.Axioms
import uv2_erc20.CtxGas

-- Untrusted proof script: the kernel checks it. The statement speaks only of the generated
-- program and its guarded copy.

/-!
# UniswapV2ERC20.transfer: the guard stage

On every call whose selector is `transfer(address,uint256)`'s, under every oracle, the final EVM
IR `evm11` and `CtxGas.guarded` (each block of `CtxGas.F`, the blocks of the other functions, a
jump to itself) end within `N` blocks in the same result: no such call enters a block the checker
with contexts and gas leaves unchecked. Symbolic execution (`sym_exec`) over a symbolic call and
oracle: the calldata, the storage and the oracle stay opaque.
-/

namespace SolarTV.Export.UniswapV2ERC20.CtxGas

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

/-- The blocks a call of transfer runs, at most: dispatch, entry, the balance read, the checked
subtraction, the credit, and the return or the revert. -/
def N : Nat := 7

/-- A call of transfer: its first calldata word's top four bytes are the selector `0xa9059cbb`. -/
def TransferCall (call : Call) : Prop :=
  EvmRules.Evm.shr 224 (calldataWord call 0) = 0xa9059cbb

set_option maxHeartbeats 8000000 in
theorem guarded_run7 (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xa9059cbb) :
    EVM.Program.run o SolarTV.Export.UniswapV2ERC20.evm11 call 7 = EVM.Program.run o guarded call 7 := by
  sym_exec

set_option maxHeartbeats 8000000 in
theorem guarded_ends7 (o : Oracle) (call : Call)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 0xa9059cbb) :
    (EVM.Program.run o guarded call 7).isSome = true := by
  sym_exec

/-- The run of the final EVM IR (with RETURNDATASIZE in effect form, the same runs) is the guarded
program's on a call of transfer. -/
theorem guard_run (o : Oracle) (call : Call) (h : TransferCall call) :
    EVM.Program.run o (SolidCore.Refinement.Solar.AssembleCtx.norm prog) call N =
      EVM.Program.run o
        (SolidCore.Refinement.Solar.AssembleCtxGas.guard F (SolidCore.Refinement.Solar.AssembleCtx.norm prog))
        call N := by
  rw [guarded_eq, SolidCore.Refinement.Solar.AssembleCtx.run_norm]
  exact guarded_run7 o call h

/-- The guarded program ends within `N` blocks on a call of transfer. -/
theorem guard_ends (o : Oracle) (call : Call) (h : TransferCall call) :
    (EVM.Program.run o
      (SolidCore.Refinement.Solar.AssembleCtxGas.guard F (SolidCore.Refinement.Solar.AssembleCtx.norm prog))
      call N).isSome = true := by
  rw [guarded_eq]
  exact guarded_ends7 o call h

/-- info: 'SolarTV.Export.UniswapV2ERC20.CtxGas.guard_ends' depends on axioms within [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#axioms_within guard_ends

/-- info: 'SolarTV.Export.UniswapV2ERC20.CtxGas.guard_run' depends on axioms within [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#axioms_within guard_run

end SolarTV.Export.UniswapV2ERC20.CtxGas
