import SolidCore.Refinement.Solar.Counter.Lowering
import SolidCore.Refinement.Evm.WideStorage
import SolidCore.Refinement.Solar.AssembleSim
import counter.Proofs.Stages
import counter.Proofs.Assembly
import counter.gen.Counter.Manifest

/-!
# counter: solar's final EVM IR to its bytecode on EthLib

The assembly stage of Counter (Spec.lean): from the final EVM IR solar compiles
(`SolarTV.Export.Counter.evm5`, after the last `cfg-simplify-early`) to its 83 bytes of runtime
bytecode `code` on EthLib, on every call of `scope`.

* `bytes_exported`: `code` is the bytecode solar exported with its stages, byte for byte.
* `evmir_run`: SolarTV's EVM IR semantics runs `evm5` on every call of `inc(d)` to `expected d`,
  from the source stage's MIR run (`mir_run`) and the backend stages
  (`SolarTV.Milestone.Counter.counter_mir_to_evmir`, on every call), under every oracle.
* `target_run`: EthLib runs `code` on every such call to `expected d`: every opcode stepped by
  EthLib's program logic from pc 0 with 10M gas (`counter_one`: `wide_tgt_s`'s steps and
  SLOAD), SLOAD's read and SSTORE's write and price included, and its branches decided from the call data.
* `stage`: the stage, under every oracle, from the generic theorem for every program and code
  the checker accepts (`Assemble.stage_of_check`, AssembleSim.lean) at `check_ok`, the kernel's
  evaluation of the checker on `evm5`, `code` and `cert`. `stage_run` proves the same stage
  from `evmir_run` and `target_run`, as a cross-check.
* `stageAnyStorage`: the same stage on every call of `inc` with no value from any storage,
  from the same check.
* `mutantAdd_check`, `mutantStore_check`: the checker rejects the two one-byte mutants of
  Milestone.lean, SUB for the ADD of `x + d` and SLOAD for the SSTORE of slot 0.

solar-tv's `SolarTV.Milestone.Counter.decodes` separately checks the bytecode's linear decoding
against `evm5`'s instructions, the walk of the assembly checker.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide

/-- The runtime bytecode's bytes. -/
def bytes : List Nat := code.data.toList.map (·.toNat)

/-- `code` is the bytecode solar exported with its stages. -/
theorem bytes_exported : bytes = SolarTV.Export.Counter.bytecode := by decide

/-- SolarTV's EVM IR semantics runs Counter's final EVM IR on every call of `inc(d)`, under
every oracle, to the observable `expected d`. -/
theorem evmir_run (o : SolarTV.Machine.Oracle) (d : U256) :
    (SolarTV.evmirSem o).run SolarTV.Export.Counter.evm5 (callOf incSelector [d]) =
      some (expected d) :=
  SolarTV.Milestone.Counter.counter_mir_to_evmir o _ trivial _ (mir_run o d)

section Target

open EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

open EthLib.Execution.State in
/-- A read of the deployed (empty) storage of a call of `callOf` is zero. -/
theorem getStorage_preState_callOf (code : ByteArray) (s : Nat) (ws : List U256) (key : U256) :
    (Target.preState code (callOf s ws)).getStorage (Target.address selfAddress)
      (U256.toBeBytes key) = 0 := by
  simp [Target.preState, callOf, TransactionState.getStorage, TransactionState.ofBlock,
    StorageMap.slot, State.getStorage]

open EthLib.Execution.State in
/-- Recording reads leaves the accounts as they are. -/
theorem getAccountOptional_recordStorageRead (tx : TransactionState) (a : Address) (k : Bytes32)
    (b : Address) : (tx.recordStorageRead a k).getAccountOptional b = tx.getAccountOptional b :=
  rfl

open EthLib.Execution.State in
/-- The storage after SLOAD, SSTORE's own read and its write, from the empty storage of a call
of `callOf`: the written word at its key, zero elsewhere. -/
theorem getStorage_writeOf_read (code : ByteArray) (s : Nat) (ws : List U256) (a1 a2 a : Address)
    (k1 k2 k : Bytes32) (v : U256) (a' : Address) (k' : Bytes32) :
    (writeOf (((Target.preState code (callOf s ws)).recordStorageRead a1 k1).recordStorageRead
      a2 k2) a k v).getStorage a' k' = if a' = a ∧ k' = k then v else 0 :=
  getStorage_writeOf code (callOf s ws) rfl a k v a' k'

open Lean.Parser.Tactic in
/-- Steps one opcode of a path of `inc`: SLOAD of the empty storage (zero, a cold key: no key
is warm at the frame's start), SSTORE after it,
STOP with the storage after the read and the write, and every other opcode as `wide_one_s`. -/
syntax "counter_one" " [" simpLemma,* "]" " [" simpLemma,* "]" ident ident ident : tactic

macro_rules
  | `(tactic| counter_one [$ls,*] [$ns,*] $hf $hstat $htgt) => `(tactic| ((try unfold Spec) <;> first
      | (refine' Triple.seq (sload (cold := true) (by decide) ?lt ?op ?cold ?gas) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case cold => simp [Substate.empty]
         case gas => simp only [ite_true]; omega) <;>
        (try simp only [$htgt:ident, getStorage_preState_callOf, Bool.true_eq, ↓reduceIte,
          Nat.reduceSub]) <;> evm_tidy
      | (refine' Triple.seq (sstore (by decide) (by decide) ?lt ?op $hstat rfl ?stip ?gas
          (setStorage_ok _ _ ?acc)) ?next
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case stip => simp only [CALL_STIPEND]; omega
         case gas => exact Nat.le_trans (sstoreCost_le _ _ _ _) (by omega)
         case acc => simp only [getAccountOptional_recordStorageRead, $htgt:ident]
                     exact account_preState _ _) <;> evm_tidy
      | (refine stop_postS ?lt ?op ?succ ?out rfl ?store
         case lt => evm_code [$ls,*]
         case op => evm_code [$ls,*]
         case succ => rfl
         case out => rfl
         case store => intro slot; rw [$htgt:ident, getStorage_writeOf_read]; wide_store)
      | wide_one_s [$ls,*] [$ns,*] $hf $hstat $htgt))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- EthLib runs solar's bytecode on every call of `inc(d)` to the observable `expected d`. -/
theorem target_run (d : U256) :
    Target.run code (callOf incSelector [d]) = some (expected d) := by
  have he : expected d =
      ⟨true, [], [], fun slot => if slot % 2 ^ 256 = 0 then d.toNat else 0⟩ := rfl
  rw [he]
  refine run_of_postS code incSelector [d] _ rfl (fun h => by cases h) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [incSelector] at hd
  repeat counter_one [code, runtimeNat, runtimeSize, incSelector] [hd, hv] hfork hstat htgt

end Target

/-- The assembly stage of Counter by running both sides to the same observable, a cross-check of
`stage`. -/
theorem stage_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scope := by
  intro call hc obs hrun
  obtain ⟨d, rfl⟩ := scope_callOf hc
  rw [evmir_run o d] at hrun
  cases hrun
  exact target_run d

/-- info: 'SolidCore.Refinement.Solar.Counter.stage_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage_run

/-! ## The stage from the generic theorem -/

/-- The certificate of the check: each block's offset in the code (bb4 at 0x34, bb10 at 0x38,
bb8 at 0x41), the stack height each block needs on entry (none), and the bound on memory (64
bytes, the end of the panic's revert data). -/
def cert : Assemble.Cert := { offsets := [0, 0x34, 0x38, 0x41], needs := [0, 0, 0, 0], top := 64 }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the final EVM IR, by the kernel's evaluation. -/
theorem check_ok : Assemble.check SolarTV.Export.Counter.evm5 code cert = true := by
  decide +kernel

theorem scope_value {call : Call} (h : scope call) : call.callvalue = 0 := by
  obtain ⟨d, rfl⟩ := scope_callOf h
  rfl

/-- **The assembly stage of Counter**: EVM IR to bytecode on EthLib, on every call of `scope`,
under every oracle. It is the generic theorem for every program and code the checker accepts,
at `check_ok`. -/
theorem stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scope :=
  Assemble.stage_of_check check_ok o fun _ h => scope_value h

/-- The assembly stage of Counter on every call of `inc` with no value from any storage `σ`, under
every oracle, from the same check. -/
theorem stageAnyStorage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code
      (fun call => ∃ σ, fullScope fns σ call) :=
  Assemble.stage_of_check check_ok o fun _ ⟨_, _, _, _, _, _, h⟩ => by rw [h]

/-- The assembly stage of Counter on every call, with any value, call data and storage, under
every oracle, from the same check. -/
theorem stageAll (o : SolarTV.Machine.Oracle) (scope : Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scope :=
  Assemble.stage_of_check_all check_ok o scope

/-- `code` with SUB (0x03) for the ADD of `x + d` at offset 42. -/
def mutantAddCode : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat
  0x346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581039081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd
  runtimeSize

/-- `code` with SLOAD (0x54) for the SSTORE of slot 0 at offset 50. -/
def mutantStoreCode : ByteArray := EthLib.Execution.Evm.Logic.NatCode.ofNat
  0x346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f54005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd
  runtimeSize

set_option maxRecDepth 100000 in
/-- The checker rejects the ADD mutant: its walk decodes SUB where the program has ADD. -/
theorem mutantAdd_check : Assemble.check SolarTV.Export.Counter.evm5 mutantAddCode cert = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checker rejects the SSTORE mutant: its walk decodes SLOAD where the program has SSTORE. -/
theorem mutantStore_check :
    Assemble.check SolarTV.Export.Counter.evm5 mutantStoreCode cert = false := by
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.Counter.stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage

/-- info: 'SolidCore.Refinement.Solar.Counter.stageAnyStorage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAnyStorage

/-- info: 'SolidCore.Refinement.Solar.Counter.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.Counter.mutantAdd_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutantAdd_check

/-- info: 'SolidCore.Refinement.Solar.Counter.mutantStore_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutantStore_check

end SolidCore.Refinement.Solar.Counter
