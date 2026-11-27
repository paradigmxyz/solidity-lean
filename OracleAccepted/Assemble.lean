import SolidCore.Refinement.Solar.AssembleDynCopy
import SolidCore.Refinement.Solar.AssembleRevert

/-!
# Oracle allow-list corollaries: the assembly back lemmas

The simplification pass changed or removed these declarations. The oracle
(/home/hand/simp/oracle/oracle.sh with the allow-list ACCEPTED.md) accepts each change
only because the new statement is at least as strong as the base's (550ff580). Each theorem below
restates a base statement verbatim, under the same name in a `Base` namespace, and
proves it from the declaration that replaced it, in one line. Nothing imports this module.
-/

namespace SolidCore.Refinement.Solar.AssembleDyn.Base

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

variable {rd : ByteArray}

/-- Base `mstore_back` (a run that succeeds), from the new `mstore_back` (one that succeeds or reverts). -/
theorem mstore_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o v : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: v :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
          (wordBytes v))
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  _root_.SolidCore.Refinement.Solar.AssembleDyn.mstore_back hat hlt hbyte within hrun (.inl hok)

/-- Base `mload_back` (a run that succeeds), from the new `mload_back` (one that succeeds or reverts). -/
theorem mload_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + (extendMemory M.size [(o, 32)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (loadWord (memoryReadBytes
          (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat 32) 0 32 :: T)
        (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy)
        (g - (3 + (extendMemory M.size [(o, 32)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  _root_.SolidCore.Refinement.Solar.AssembleDyn.mload_back hat hlt hbyte within hrun (.inl hok)

/-- Base `keccak_back` (a run that succeeds), from the new `keccak_back` (one that succeeds or reverts). -/
theorem keccak_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {o sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (o :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1)
        (keccak (memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
          o.toNat sz.toNat) :: T)
        (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (keccak256Cost sz + (extendMemory M.size [(o, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  _root_.SolidCore.Refinement.Solar.AssembleDyn.keccak_back hat hlt hbyte within hrun (.inl hok)

/-- Base `log_back` (a run that succeeds), from the new `log_back` (one that succeeds or reverts). -/
theorem log_back {n : Fin 5} {byte : UInt8} {code : ByteArray} {msg : Message .fusaka} {pc : Nat}
    {o sz : Word} {words T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} {evm : Evm .fusaka Nat}
    (hat : At code msg pc (o :: sz :: (words ++ T)) M g st ss rd evm)
    (hlen : words.length = n.val) (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (decoded : Op.decode byte = some (.log n)) (hstatic : msg.isStatic = false) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    logCost n.val sz + (extendMemory M.size [(o, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
        (g - (logCost n.val sz + (extendMemory M.size [(o, sz)]).cost)) st
        { ss with
          logs := ss.logs.push
            { address := msg.currentTarget
              topics := words.map U256.toBeBytes
              data := memoryReadBytes (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy)
                o.toNat sz.toNat } } rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  _root_.SolidCore.Refinement.Solar.AssembleDyn.log_back hat hlen hlt hbyte decoded hstatic within hrun (.inl hok)

end SolidCore.Refinement.Solar.AssembleDyn.Base

namespace SolidCore.Refinement.Solar.AssembleDynCopy.Base

open SolarTV SolarTV.Machine SolidCore.Refinement
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleDyn SolidCore.Refinement.Solar.AssembleEffects
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Wide

variable {rd : ByteArray}

/-- Base `cdc_back` (a run that succeeds), from the new `cdc_back` (one that succeeds or reverts). -/
theorem cdc_back {code : ByteArray} {msg : Message .fusaka} {pc : Nat} {d off sz : Word}
    {T : List Word} {M : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate}
    {evm : Evm .fusaka Nat} (hat : At code msg pc (d :: off :: sz :: T) M g st ss rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) {bound : Nat}
    {runChild : MessageRunner .fusaka Nat bound} (within : GasMeter.gasHeld evm.gas ≤ bound)
    {fin : Evm .fusaka Nat}
    (hrun : runFrame (step .fusaka) (step_decreases .fusaka) bound runChild evm within = .ok fin)
    (hok : fin.error = none) :
    3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost ≤ g ∧
    ∃ (m : Evm .fusaka Nat) (within' : GasMeter.gasHeld m.gas ≤ bound),
      At code msg (pc + 1) T
        (memoryWrite (memoryExtend M (extendMemory M.size [(d, sz)]).expandBy)
          d.toNat ⟨(bufferRead msg.data off.toNat sz.toNat).toArray⟩)
        (g - (3 + 3 * wordCount sz.toNat + (extendMemory M.size [(d, sz)]).cost)) st ss rd m ∧
      runFrame (step .fusaka) (step_decreases .fusaka) bound runChild m within' = .ok fin :=
  _root_.SolidCore.Refinement.Solar.AssembleDynCopy.cdc_back hat hlt hbyte within hrun (.inl hok)

end SolidCore.Refinement.Solar.AssembleDynCopy.Base

namespace SolidCore.Refinement.Solar.AssembleLoop.Base

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolarTV

/-- Base `processMessage_frame` (some runner of child messages), from the new one, which names
the runner: the interpreter's `processRunner`. -/
theorem processMessage_frame {message : Message .fusaka}
    (hpre : precompileAddress .fusaka message = none) {st : TransactionState} {ss : Substate} {evm}
    (hr : processMessage (Meter := Nat) .fusaka message st ss = .ok evm) :
    ∃ (st' : TransactionState) (ss' : Substate) (runChild : MessageRunner .fusaka Nat message.gas)
      (within : GasMeter.gasHeld (startFrame message st' ss' message.gas).gas ≤ message.gas)
      (fr : Evm .fusaka Nat),
      (¬ (message.shouldTransferValue = true ∧ message.value ≠ 0) → st' = st ∧ ss' = ss) ∧
      ((message.shouldTransferValue = true ∧ message.value ≠ 0) →
        st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st' ∧
        ss' = { ss with logs := (pushTransferLog .fusaka ss.logs message.caller message.currentTarget
          message.value) }) ∧
      runFrame (step .fusaka) (step_decreases .fusaka) message.gas runChild
        (startFrame message st' ss' message.gas) within = .ok fr ∧
      evm.1.error = fr.error ∧ evm.1.output = fr.output :=
  let ⟨st', ss', within, fr, h⟩ := _root_.SolidCore.Refinement.Solar.AssembleLoop.processMessage_frame hpre hr
  ⟨st', ss', _, within, fr, h⟩

end SolidCore.Refinement.Solar.AssembleLoop.Base
