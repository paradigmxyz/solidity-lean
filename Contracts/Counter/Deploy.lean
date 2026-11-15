import SolidCore.Refinement.Evm.Wide
import SolidCore.Refinement.Solar.Counter.Spec
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# Counter: deployment

solar's init code for the counter milestone (`-Ogas --evm-version osaka`, the same compiler and
options as the runtime bytecode `code`) is 17 bytes of constructor followed by the 83 bytes of
runtime:

    CALLVALUE PUSH1 0x0d JUMPI            ; not payable
    PUSH1 0x53 DUP1 PUSH1 0x11 PUSH0      ; 83 bytes from offset 17 to memory 0
    CODECOPY PUSH0 RETURN                 ; return them
    JUMPDEST PUSH0 PUSH0 REVERT

* `initcode_runs`: EthLib runs the init code, in one frame with no value, no call data and the
  empty storage, to success, writing no storage and emitting no log, and returns exactly the
  runtime bytecode `code` the rest of the certificate is about.
* `initcode_runtime`: the init code ends with the runtime bytecode, byte for byte.

The frame runs the init code as the code at the contract's address, as a creation does: CODECOPY
reads the running code, which is the init code. Not covered: the creation message's address
derivation and the code deposit of `processCreateMessage` (EIP-3541's `0xef` check and the
24576-byte limit, which `deposit_ok` checks of `code` separately).
-/

namespace SolidCore.Refinement.Solar.Counter.Deploy

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex
open SolidCore.Refinement.Evm.Wide

/-- The init code solar emits for Counter, read big-endian. -/
def initNat : Nat :=
  0x34600d5760538060115f395ff35b5f5ffd346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd

/-- The init code's length in bytes: 17 of constructor and the 83 of runtime. -/
def initSize : Nat := 100

/-- solar's init code for Counter. -/
def initcode : ByteArray := NatCode.ofNat initNat initSize

/-- The init code ends with the runtime bytecode. -/
theorem initcode_runtime :
    (initcode.data.toList.drop 17) = code.data.toList := by decide +kernel

/-- The deployment: no call data, no value, the empty storage. -/
def deployCall : Call := { calldata := .empty, callvalue := 0, storage := [] }

/-- What the deployment shows: success, the runtime bytecode as output, no log, no storage. -/
def deployed : Observable :=
  { success := true, output := code.data.toList.map (·.toNat), logs := [], storage := fun _ => 0 }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The frame of the init code, for every message with no value, from every state: it steps
CALLVALUE, the untaken JUMPI, the pushes, CODECOPY and RETURN by EthLib's program logic. -/
theorem frame (msg : Message .fusaka) (hv : msg.value = 0) (st : State.TransactionState)
    (ss : Substate) :
    Spec .fusaka (At initcode msg 0 [] .empty 10000000 st ss .empty) (Post deployed st ss) := by
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize, hv]
  evm_step [initcode, initNat, initSize, hv]
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize]
  evm_step [initcode, initNat, initSize]
  refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?beforeCopy
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => evm_gas
  case room => evm_room
  all_goals evm_tidy
  refine' Triple.seq (codecopy ?lt ?op ?gas) ?afterCopy
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => wide_mem
  all_goals evm_tidy
  refine' Triple.seq (push0 (by decide) ?lt ?op ?gas ?room) ?afterPush
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => wide_mem
  case room => evm_room
  all_goals evm_tidy
  refine return_post ?lt ?op ?gas rfl ?out
  case lt => evm_code [initcode, initNat, initSize]
  case op => evm_code [initcode, initNat, initSize]
  case gas => decide +kernel
  case out => decide +kernel

/-- **solar's init code deploys the runtime bytecode.** EthLib runs Counter's init code in one
frame, with no value, no call data and the empty storage, to success: it returns exactly the
83-byte runtime bytecode `code` (the bytecode `spec_holds_of_bytecode` is about), writes no
storage and emits no log. -/
theorem initcode_runs : Target.run initcode deployCall = some deployed := by
  obtain ⟨evm, hr, herr, hout, hsub, hst⟩ := processMessage_post (Target.message initcode deployCall)
    rfl rfl (precompileAddress_message initcode deployCall) deployed
    (fun st ss => frame _ rfl st ss) (Target.preState initcode deployCall) Substate.empty
  simp only [Target.run, hr]
  have hsucc : evm.1.error.isNone = true := by rw [herr]; rfl
  congr 1
  simp only [deployed, Observable.mk.injEq]
  refine ⟨hsucc, hout, by simp [hsub, Substate.empty], ?_⟩
  funext slot
  simp only [hsucc, ↓reduceIte]
  rw [hst rfl, getStorage_preState_nil initcode deployCall rfl slot]
  rfl

/-- The returned code passes the deposit's checks: it does not start with `0xef` (EIP-3541)
and fits in 24576 bytes (EIP-170). -/
theorem deposit_ok : code.size ≤ 24576 ∧ code.data.toList.head? ≠ some 0xef := by
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.Counter.Deploy.initcode_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initcode_runs

/-- info: 'SolidCore.Refinement.Solar.Counter.Deploy.deposit_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms deposit_ok

end SolidCore.Refinement.Solar.Counter.Deploy
