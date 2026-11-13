import SolidCore.Solidity.Checked
import EthLib.Execution.Evm.Call.MessageCall
import SolarTV.Sem

/-!
# Refinement of solar's runtime bytecode against SolidCore

This module states, once, what it means for compiled bytecode to implement a
contract of the source semantics.

A call runs on both sides with the same call data, call value and initial
storage of the callee:

* `Source.run` constructs the contract in SolidCore, replaces its storage with
  the call's initial storage and calls it through the ABI dispatcher
  (`CheckedContract.callCalldataAtFromWithContext?`);
* `Target.run` installs the bytecode at `selfAddress` in EthLib's state and runs
  one `processMessage` from `callerAddress` at the Fusaka fork.

Each side yields an `Observable`: whether the call succeeded, its return or
revert data, the logs it emitted and the callee's final storage.
`Refines fuel contract code scope` says that for every call in `scope` both
sides produce the same observable.

## Assumptions

The statement fixes the following, and a theorem about it proves nothing
outside them:

* **One frame, fixed environment.** The caller is `callerAddress`, the callee
  `selfAddress`, the fork Fusaka, and the block and transaction environment
  `Target.blockEnv` and `Target.txEnv`. Contracts that read the block, the
  origin, balances or other accounts, or that call out, are out of scope.
* **Gas.** The message carries `gasLimit` gas. A call the source semantics
  completes but the bytecode runs out of gas on is a counterexample, not an
  excluded case, so a theorem must show the bytecode stays within it.
* **Deployment.** `Target.run` starts from the runtime bytecode with the call's
  storage, while `Source.run` runs the constructor first and then overwrites
  storage. Contracts whose constructor leaves other state (immutables, logs)
  are out of scope.
* **Failure.** A failed call keeps the initial storage and emits no logs on
  both sides, so `Observable` records exactly that rather than either
  semantics' intermediate state.
* **Keccak.** SolidCore hashes with evmyul's Keccak-256 and EthLib with its own.
  A theorem about a contract that hashes (mappings, dynamic arrays, events with
  signatures) must prove the two agree on the inputs it uses.
* **Fuel.** SolidCore's interpreter takes fuel; `Refines` fixes it, and running
  out of fuel makes `Source.run` return `none`, which refutes the statement.
-/

namespace SolidCore.Refinement

-- One external call (Call), what it shows outside the callee (Observable) and the
-- value of a slot in a call's storage (slotValue) are solar's SolarTV.Sem definitions,
-- used directly so that a stage solar proves is a stage of this library with no bridge.
-- A Call is the call data, the call value and the callee's storage before the call as
-- (slot, value) pairs, where a later pair for the same slot wins; an Observable is whether
-- the call returned, its return or revert data, its logs (empty when it failed) as topics
-- and data bytes, and the callee's storage after it (its initial storage when it failed).
export SolarTV (Call Call.mk Observable Observable.mk Observable.mk.injEq slotValue)

/-- The account that sends every call. -/
def callerAddress : Nat := 0x2000

/-- The account the contract runs at. -/
def selfAddress : Nat := 0x1000

/-- The gas every call carries. -/
def gasLimit : Nat := 10000000

namespace Source

open SolidCore.Solidity SolidCore.Solidity.Source

/-- SolidCore's result for `call` against `contract` with `fuel`: construct the
contract, replace its storage with the call's and call it through the ABI
dispatcher. `none` when the interpreter fails, runs out of fuel or the constructor
reverts. -/
def result? (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  let base := contract.core.context
  let context :=
    { base with sender := callerAddress, self := selfAddress, value := call.callvalue }
  match TypeCheck.CheckedContract.constructWithContext? fuel contract context
      State.empty selfAddress 0 [] with
  | some (CallResult.returned deployed _) =>
    let storage := call.storage.foldl
      (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) deployed.storage
    TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel contract context
      { deployed with storage := storage } selfAddress callerAddress call.callvalue
      (call.calldata.data.toList.map (·.toNat))
  | _ => none

/-- SolidCore's result for `call` from the account `caller`: the contract is constructed as
`result?` constructs it (from `callerAddress`, its deployer), its storage replaced with the
call's, and then called through the ABI dispatcher from `caller`, which the dispatcher's call
context takes as `msg.sender`. From `callerAddress` it is `result?`
(`resultFrom?_callerAddress`). -/
def resultFrom? (caller : Nat) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  let base := contract.core.context
  let context :=
    { base with sender := callerAddress, self := selfAddress, value := call.callvalue }
  match TypeCheck.CheckedContract.constructWithContext? fuel contract context
      State.empty selfAddress 0 [] with
  | some (CallResult.returned deployed _) =>
    let storage := call.storage.foldl
      (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) deployed.storage
    TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel contract context
      { deployed with storage := storage } selfAddress caller call.callvalue
      (call.calldata.data.toList.map (·.toNat))
  | _ => none

theorem resultFrom?_callerAddress : resultFrom? callerAddress = result? := rfl

/-- What `result` shows outside the callee. -/
def observe (call : Call) (result : TypeCheck.CoreAbiCallResult) : Observable :=
  { success := result.success
    output := result.output
    logs :=
      if result.success then
        (result.state.logEntries selfAddress).map fun entry => (entry.topics, entry.data)
      else []
    storage := fun slot =>
      if result.success then result.state.loadSlot slot else slotValue call.storage slot }

/-- Run `call` against `contract` in SolidCore with `fuel`. -/
def run (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  (result? fuel contract call).map (observe call)

/-- Run `call` against `contract` in SolidCore with `fuel`, from the account `caller`. -/
def runFrom (caller : Nat) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  (resultFrom? caller fuel contract call).map (observe call)

theorem runFrom_callerAddress : runFrom callerAddress = run := rfl

end Source

namespace Target

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.State

/-- The 20-byte address with value `n`. -/
def address (n : Nat) : Address :=
  ⟨(natToBytes 20 n).toArray, by simp [natToBytes_length]⟩

/-- The 32-byte storage key with value `n`. -/
def storageKey (n : Nat) : Bytes32 :=
  ⟨(natToBytes 32 n).toArray, by simp [natToBytes_length]⟩

/-- The block every call runs in. -/
def blockEnv : BlockEnvironment .fusaka :=
  { chainId := 1, coinbase := address 0, number := 1, gasLimit := 30000000, timestamp := 1,
    difficulty := 0, blockHashes := [], baseFeePerGas := fun _ => 0,
    prevRandao := fun _ => storageKey 0, excessBlobGas := fun _ => 0,
    parentBeaconBlockRoot := fun _ => (default : Hash32), slotNumber := fun _ => 0 }

/-- The transaction every call belongs to. -/
def txEnv : TransactionEnvironment .fusaka :=
  { origin := address callerAddress, gasPrice := 0, blobVersionedHashes := fun _ => [] }

/-- The state before the call: `code` at `selfAddress` with the call's storage,
and a caller that holds exactly the call value. -/
def preState (code : ByteArray) (call : Call) : TransactionState :=
  let hash := EthLib.Cryptography.Hash.Keccak.keccak256 code
  let storage : Std.ExtTreeMap Bytes32 U256 :=
    call.storage.foldl (fun m kv => m.insert (storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅
  let pre : State :=
    { accounts := ((∅ : Std.ExtTreeMap Address Account).insert (address selfAddress)
          { nonce := 1, balance := 0, codeHash := hash }).insert (address callerAddress)
          { nonce := 0, balance := BitVec.ofNat 256 call.callvalue,
            codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 .empty },
      storage := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert
        (address selfAddress) storage,
      code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert hash code }
  TransactionState.ofBlock
    { preState := pre, accountWrites := ∅, storageWrites := ∅, codeWrites := ∅,
      storageClears := ∅ }

/-- The message of the call: `gasLimit` gas from `callerAddress` to `selfAddress`. -/
def message (code : ByteArray) (call : Call) : Message .fusaka :=
  { blockEnv, txEnv, caller := address callerAddress, target := some (address selfAddress),
    currentTarget := address selfAddress, gas := gasLimit, value := call.callvalue,
    data := call.calldata, codeAddress := some (address selfAddress),
    code, depth := 0, shouldTransferValue := true, isStatic := false,
    disablePrecompiles := false }

/-- Run `call` against `code` in EthLib. `none` when `processMessage` raises. -/
def run (code : ByteArray) (call : Call) : Option Observable :=
  match processMessage (Meter := Nat) .fusaka (message code call) (preState code call)
      Substate.empty with
  | .error _ => none
  | .ok ⟨evm, _⟩ =>
    let success := evm.error.isNone
    some
      { success
        output := evm.output.toList.map (·.toNat)
        logs :=
          if success then
            evm.substate.logs.toList.map fun log =>
              (log.topics.map fun topic => bytesToNat topic.toList,
                log.data.toList.map (·.toNat))
          else []
        storage := fun slot =>
          if success then (evm.state.getStorage (address selfAddress) (storageKey slot)).toNat
          else slotValue call.storage slot }

/-- The transaction of a call from the account `caller`, its origin. -/
def txEnvFrom (caller : Nat) : TransactionEnvironment .fusaka :=
  { origin := address caller, gasPrice := 0, blobVersionedHashes := fun _ => [] }

/-- The state before a call from the account `caller`: `code` at `selfAddress` with the
call's storage, and `caller` holding exactly the call value. -/
def preStateFrom (caller : Nat) (code : ByteArray) (call : Call) : TransactionState :=
  let hash := EthLib.Cryptography.Hash.Keccak.keccak256 code
  let storage : Std.ExtTreeMap Bytes32 U256 :=
    call.storage.foldl (fun m kv => m.insert (storageKey kv.1) (BitVec.ofNat 256 kv.2)) ∅
  let pre : State :=
    { accounts := ((∅ : Std.ExtTreeMap Address Account).insert (address selfAddress)
          { nonce := 1, balance := 0, codeHash := hash }).insert (address caller)
          { nonce := 0, balance := BitVec.ofNat 256 call.callvalue,
            codeHash := EthLib.Cryptography.Hash.Keccak.keccak256 .empty },
      storage := (∅ : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256)).insert
        (address selfAddress) storage,
      code := (∅ : Std.ExtTreeMap Hash32 ByteArray).insert hash code }
  TransactionState.ofBlock
    { preState := pre, accountWrites := ∅, storageWrites := ∅, codeWrites := ∅,
      storageClears := ∅ }

/-- The message of a call from the account `caller`: `gasLimit` gas to `selfAddress`. -/
def messageFrom (caller : Nat) (code : ByteArray) (call : Call) : Message .fusaka :=
  { blockEnv, txEnv := txEnvFrom caller, caller := address caller,
    target := some (address selfAddress),
    currentTarget := address selfAddress, gas := gasLimit, value := call.callvalue,
    data := call.calldata, codeAddress := some (address selfAddress),
    code, depth := 0, shouldTransferValue := true, isStatic := false,
    disablePrecompiles := false }

/-- Run `call` against `code` in EthLib from the account `caller` (its sender and origin).
From `callerAddress` it is `run` (`runFrom_callerAddress`). -/
def runFrom (caller : Nat) (code : ByteArray) (call : Call) : Option Observable :=
  match processMessage (Meter := Nat) .fusaka (messageFrom caller code call)
      (preStateFrom caller code call) Substate.empty with
  | .error _ => none
  | .ok ⟨evm, _⟩ =>
    let success := evm.error.isNone
    some
      { success
        output := evm.output.toList.map (·.toNat)
        logs :=
          if success then
            evm.substate.logs.toList.map fun log =>
              (log.topics.map fun topic => bytesToNat topic.toList,
                log.data.toList.map (·.toNat))
          else []
        storage := fun slot =>
          if success then (evm.state.getStorage (address selfAddress) (storageKey slot)).toNat
          else slotValue call.storage slot }

theorem preStateFrom_callerAddress : preStateFrom callerAddress = preState := rfl

theorem messageFrom_callerAddress : messageFrom callerAddress = message := rfl

theorem runFrom_callerAddress : runFrom callerAddress = run := by
  funext code call
  simp only [runFrom, run, messageFrom_callerAddress, preStateFrom_callerAddress]
  split <;> rename_i h <;> rw [h]

end Target

/-- `code` implements `contract` on every call `scope` admits: SolidCore with
`fuel` and EthLib both finish and show the same observable. -/
def Refines (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (scope : Call → Prop) : Prop :=
  ∀ call, scope call →
    ∃ obs, Source.run fuel contract call = some obs ∧ Target.run code call = some obs

end SolidCore.Refinement

