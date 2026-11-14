import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Call.Create

/-!
# CREATE2 in EthLib: the address and the steps that send no message

What CREATE2 does in EthLib's interpreter (Fusaka) beside the step that sends the init code as a
message (EthLib's `Logic.create2With`):

* `create2Address_toU256`: the new address, as the word the creator pushes, is the low 160 bits
  of Keccak-256 of `0xff`, the creator's address, the salt and Keccak-256 of the init code (EIP-1014).
* `createStep2_oog`: short of the price of the creation and the growth of memory, the step fails.
* `createStep2_skip`: a creator that lacks the value, holds the greatest nonce, or is at the
  greatest depth runs no message: it pays the price, grows memory, pushes 0 and goes on, with empty
  return data and only the read of its own account recorded.
* `createStep2_collision`: an address that holds code or a nonce gets no message: the creator pays
  the gas it would pass on as well, its nonce grows, and it pushes 0 (EIP-684).
-/

namespace SolidCore.Refinement.Solar.AssembleCreate

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The address -/

/-- The address in a hash, as a word, is the hash's word modulo `2 ^ 160`: its last 20 bytes. -/
theorem addressOfHash_toU256 (h : Vector UInt8 32) :
    (addressOfHash h).toU256 = BitVec.ofNat 256 ((U256.fromBeBytes h).toNat % 2 ^ 160) := by
  have hsplit : h.toList = h.toList.take 12 ++ h.toList.drop 12 := (List.take_append_drop 12 _).symm
  have hlen : (h.toList.drop 12).length = 20 := by simp
  have hlt := bytesToNat_lt (h.toList.drop 12)
  rw [hlen, show (256 : Nat) ^ 20 = 2 ^ 160 from rfl] at hlt
  have hall := bytesToNat_lt h.toList
  simp only [Vector.length_toList] at hall
  unfold Address.toU256 addressOfHash U256.fromBeBytes
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bytesToNat h.toList < 2 ^ 256)]
  congr 1
  have hd : (h.drop 12).toList = h.toList.drop 12 := by
    simp only [Vector.drop]
    simp
    have h20 : (List.drop 12 h.toArray.toList).length ≤ 20 := Nat.le_of_eq hlen
    rw [List.take_of_length_le h20]
    rfl
  rw [hd]
  conv => rhs; rw [hsplit, bytesToNat_append, hlen]
  rw [show (256 : Nat) ^ 20 = 2 ^ 160 from rfl, Nat.mul_comm (bytesToNat _) (2 ^ 160),
    Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- **The CREATE2 address** (EIP-1014), as the word the creator pushes: the low 160 bits of the
Keccak-256 word of its preimage, `0xff`, the sender's 20 bytes, the salt's 32 bytes and the 32 bytes of the
Keccak-256 word of the init code (`create2Preimage`). -/
theorem create2Address_toU256 (sender : Address) (salt : U256) (initCode : ByteArray) :
    (create2Address sender salt initCode).toU256 = BitVec.ofNat 256 ((keccak
      (create2Preimage sender salt (U256.toBeBytes (keccak initCode)))).toNat % 2 ^ 160) := by
  have e : U256.toBeBytes (keccak initCode) = keccak256 initCode := U256.toBeBytes_fromBeBytes _
  rw [e]
  exact addressOfHash_toU256 _

/-- info: 'SolidCore.Refinement.Solar.AssembleCreate.create2Address_toU256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms create2Address_toU256


/-! ## The steps of CREATE2 that send no message -/

/-- The price CREATE2 pays at Fusaka before the gas it passes on: 32000, 6 gas a word to hash the
init code, 2 gas a word of init code (EIP-3860) and the growth of memory. -/
def cost2 (msize : Nat) (start size : U256) : Nat :=
  createBaseCost .fusaka + OPCODE_KECCAK256_PER_WORD * wordCount size.toNat +
    initCodeCost size.toNat + (extendMemory msize [(start, size)]).cost

theorem cost2_eq (msize : Nat) (start size : U256) :
    cost2 msize start size = createBaseCost .fusaka +
      (if true then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0) +
      (if Fork.fusaka ≥ .shapella then initCodeCost size.toNat else 0) +
      (extendMemory msize [(start, size)]).cost := by
  simp [cost2, show Fork.fusaka ≥ .shapella by decide]

/-- **CREATE2 short of its price fails**: the step is an error. -/
theorem createStep2_oog {evm : Evm .fusaka Nat} {value start size salt : U256} {rest : List U256}
    (hst : evm.stack.val = value :: start :: size :: salt :: rest)
    (hgas : evm.gas < cost2 evm.memory.size start size) :
    ∃ e, createStep (fork := .fusaka) (Meter := Nat) true evm = .error e := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hgas ⊢
  subst hst
  unfold cost2 at hgas
  refine ⟨.outOfGas, ?_⟩
  simp [createStep, show ¬ Fork.fusaka ≥ .glamsterdam by decide, popWord, Stack.pop, popSalt, bind,
    Except.bind, pure, Except.pure, chargeGasAndMemory, chargeGas, GasMeter.charge,
    show Fork.fusaka ≥ .shapella by decide, hgas]

/-- The init code CREATE2 reads from memory grown for its range has the range's size. -/
theorem size_read {memory : ByteArray} (hmod : memory.size % 32 = 0) (start size : U256) :
    (memoryReadBytes (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
      start.toNat size.toNat).size = size.toNat := by
  unfold memoryReadBytes
  split
  · rename_i h; simp [h]
  · rename_i h
    have hz : size ≠ 0 := fun e => h (by simp [e])
    have hle := le_ceil32_add_expandBy memory.size [(start, size)] (start, size) (by simp) hz
    rw [ceil32_of_mod hmod] at hle
    simp only at hle
    simp only [ByteArray.size_extract, size_memoryExtend]
    omega

/-- **CREATE2 of init code past the limit of EIP-3860 fails.** -/
theorem createStep2_big {evm : Evm .fusaka Nat} {value start size salt : U256} {rest : List U256}
    (hst : evm.stack.val = value :: start :: size :: salt :: rest) (hmod : evm.memory.size % 32 = 0)
    (hgas : cost2 evm.memory.size start size ≤ evm.gas)
    (hbig : maxInitCodeSize .fusaka < size.toNat) :
    ∃ e, createStep (fork := .fusaka) (Meter := Nat) true evm = .error e := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hgas hmod ⊢
  subst hst
  unfold cost2 at hgas
  have hread := size_read hmod start size
  refine ⟨.outOfGas, ?_⟩
  simp [createStep, show ¬ Fork.fusaka ≥ .glamsterdam by decide, popWord, Stack.pop, popSalt, bind,
    Except.bind, pure, Except.pure, chargeGasAndMemory, chargeGas, GasMeter.charge,
    show Fork.fusaka ≥ .shapella by decide, Nat.not_lt.mpr hgas, genericCreate, hread, hbig]

/-- **A creator that lacks the value, holds the greatest nonce or is at the greatest depth runs no
message**: CREATE2 pays its price, grows memory, pushes 0 and goes on, with empty return data and
the read of its own account recorded. -/
theorem createStep2_skip {evm : Evm .fusaka Nat} {value start size salt : U256} {rest : List U256}
    (hst : evm.stack.val = value :: start :: size :: salt :: rest)
    (hstatic : evm.message.isStatic = false)
    (hinit : size.toNat ≤ maxInitCodeSize .fusaka)
    (hgas : cost2 evm.memory.size start size ≤ evm.gas)
    (hskip : (evm.state.getAccount evm.message.currentTarget).balance < value ∨
      (evm.state.getAccount evm.message.currentTarget).nonce = MAX_NONCE ∨
      STACK_DEPTH_LIMIT < evm.message.depth + 1) :
    ∃ after, createStep (fork := .fusaka) (Meter := Nat) true evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.memory = memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy ∧
      after.gas = evm.gas - cost2 evm.memory.size start size ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.returnData = .empty ∧
      after.state = evm.state.recordAccountRead evm.message.currentTarget ∧
      after.substate = evm.substate := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hgas hskip ⊢
  subst hst
  unfold cost2 at hgas ⊢
  have hread : (memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat).size ≤
      size.toNat := by
    unfold memoryReadBytes
    split
    · simp
    · simp only [ByteArray.size_extract]
      omega
  have hlim : ¬(Fork.shapella ≤ Fork.fusaka ∧ maxInitCodeSize .fusaka < (memoryReadBytes
      (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy) start.toNat
      size.toNat).size) := by
    rintro ⟨-, hlt⟩
    omega
  have hlen : rest.length < STACK_LIMIT := by simp at hl; unfold STACK_LIMIT at *; omega
  have hne : rest.length ≠ STACK_LIMIT := by omega
  have hlim' : ¬ maxInitCodeSize .fusaka < (memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat).size := by
    omega
  have hgd : ∀ (tx : State.TransactionState) (x : Address),
      (tx.recordAccountRead x).getAccount = tx.getAccount := fun _ _ => rfl
  simp [createStep, show ¬ Fork.fusaka ≥ .glamsterdam by decide, popWord, Stack.pop, popSalt, bind,
    Except.bind, pure, Except.pure, chargeGasAndMemory, chargeGas, GasMeter.charge,
    show Fork.fusaka ≥ .shapella by decide, Nat.not_lt.mpr hgas, genericCreate, hlim, hstatic,
    launchCreate, recordAccountRead, hgd, hskip, skipCall, pushWord, Stack.push, hne, hlim',
    GasMeter.credit, advance]
  all_goals first
    | done
    | exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- **An address that holds code or a nonce gets no message** (EIP-684): CREATE2 pays its price and
the gas it would pass on, grows memory, the creator's nonce grows, and it pushes 0 and goes on with
empty return data. -/
theorem createStep2_collision {evm : Evm .fusaka Nat} {value start size salt : U256}
    {rest : List U256}
    (hst : evm.stack.val = value :: start :: size :: salt :: rest)
    (hstatic : evm.message.isStatic = false)
    (hinit : size.toNat ≤ maxInitCodeSize .fusaka)
    (hgas : cost2 evm.memory.size start size ≤ evm.gas)
    (hbal : value ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hnonce : (evm.state.getAccount evm.message.currentTarget).nonce ≠ MAX_NONCE)
    (hdepth : evm.message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hdeploy : evm.state.accountDeployable (create2Address evm.message.currentTarget salt
      (memoryReadBytes (memoryExtend evm.memory
        (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat)) = false) :
    ∃ after st', createStep (fork := .fusaka) (Meter := Nat) true evm = .ok (.next after) ∧
      ((evm.state.recordAccountRead evm.message.currentTarget).recordAccountRead
        (create2Address evm.message.currentTarget salt (memoryReadBytes (memoryExtend evm.memory
          (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat))).incrementNonce
        .fusaka evm.message.currentTarget = .ok st' ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.memory = memoryExtend evm.memory (extendMemory evm.memory.size [(start, size)]).expandBy ∧
      after.gas = evm.gas - cost2 evm.memory.size start size -
        createMessageGas .fusaka (evm.gas - cost2 evm.memory.size start size) ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.returnData = .empty ∧ after.state = st' ∧
      after.substate = { evm.substate with
        accessedAddresses := evm.substate.accessedAddresses.insert (create2Address
          evm.message.currentTarget salt (memoryReadBytes (memoryExtend evm.memory
            (extendMemory evm.memory.size [(start, size)]).expandBy) start.toNat size.toNat)) } := by
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst hstatic hgas hbal hnonce hdepth hdeploy ⊢
  subst hst
  unfold cost2 at hgas ⊢
  have hread : (memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat).size ≤
      size.toNat := by
    unfold memoryReadBytes
    split
    · simp
    · simp only [ByteArray.size_extract]
      omega
  have hlim : ¬(Fork.shapella ≤ Fork.fusaka ∧ maxInitCodeSize .fusaka < (memoryReadBytes
      (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy) start.toNat
      size.toNat).size) := by
    rintro ⟨-, hlt⟩
    omega
  have hlen : rest.length < STACK_LIMIT := by simp at hl; unfold STACK_LIMIT at *; omega
  have hmg : ∀ g, ¬g < createMessageGas .fusaka g := by
    intro g
    simp only [createMessageGas, show Fork.fusaka ≥ .tangerineWhistle by decide, ite_true,
      maxMessageCallGas]
    omega
  have hgd : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).accountDeployable y = tx.accountDeployable y := fun _ _ _ => rfl
  generalize hA : create2Address message.currentTarget salt (memoryReadBytes (memoryExtend memory
    (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat) = A at hdeploy ⊢
  obtain ⟨state', hinc⟩ := State.TransactionState.incrementNonce_isOk .fusaka
    ((state.recordAccountRead message.currentTarget).recordAccountRead A) message.currentTarget
  have hne : rest.length ≠ STACK_LIMIT := by omega
  have hlim' : ¬ maxInitCodeSize .fusaka < (memoryReadBytes (memoryExtend memory
      (extendMemory memory.size [(start, size)]).expandBy) start.toNat size.toNat).size := by
    omega
  simp [createStep, show ¬ Fork.fusaka ≥ .glamsterdam by decide, popWord, Stack.pop, popSalt, bind,
    Except.bind, pure, Except.pure, chargeGasAndMemory, chargeGas, GasMeter.charge,
    show Fork.fusaka ≥ .shapella by decide, Nat.not_lt.mpr hgas, genericCreate, hlim, hstatic,
    launchCreate, recordAccountRead, hgd, BitVec.not_lt.mpr hbal, hnonce, Nat.not_lt.mpr hdepth,
    creationAddress, hA, accessAddress, keepReads, show Fork.berlin ≤ Fork.fusaka by decide, createNewAccountStateGas, chargeStateGas,
    GasMeter.chargeState, hmg, hdeploy, hinc, Except.mapError, GasMeter.gasLeft, pushWord,
    Stack.push, hne, hlim', advance]

end SolidCore.Refinement.Solar.AssembleCreate
