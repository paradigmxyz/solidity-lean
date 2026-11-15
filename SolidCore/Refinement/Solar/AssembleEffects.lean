import SolidCore.Refinement.Solar.RunOracle
import EthLib.Execution.Proofs.Evm.Logic.Copy
import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# EVM IR to bytecode: the instructions of a run's oracle

What each instruction that reads what the oracle of a run answers (GAS, RETURNDATASIZE,
RETURNDATACOPY) or that copies a range of dynamic size (CALLDATACOPY, RETURNDATACOPY) does in
SolarTV and in EthLib, one instruction at a time: EthLib's rule, SolarTV's effect, and that the
relations of the simulation hold after both.

* `MemRel` after a write of a range (`memRel_write`) and after the growth of memory for two ranges
  at once, as a call grows it (`memRel_expand2`).
* `RdRel o w rd`: EthLib's return data `rd` is the oracle's for SolarTV's world `w`. The oracle of a
  run meets it for the table's return data (`rdRel_table`); a log or a GAS read keeps it.
* GAS (`gas_step`) pushes EthLib's gas left when the oracle answers it, which the oracle of a run
  does for the `k`-th read with the table's `k`-th gas (`gas_step_table`). GAS is not monotone in gas, so
  its rule is a plain `Hoare` triple, not `HoareG`.
* RETURNDATASIZE (`returndatasize_step`), RETURNDATACOPY within the return data
  (`returndatacopy_step`; past its end SolarTV's effect is undefined, `returndatacopy_past`),
  CALLDATACOPY of any size (`calldatacopy_step`).
* STATICCALL (`staticcall_step`), from EthLib's `Logic.staticcallWith` under every frame that ends the
  message: the flag, the stack, memory with the callee's output written and the return data are
  SolarTV's under an oracle that answers the call's success and output as the callee ended, which
  the oracle of a run does with the callee's frame as the table's next entry (`staticcall_table`).
-/

namespace SolidCore.Refinement.Solar.AssembleEffects

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.RunOracle
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

/-! ## Memory -/

/-- A write of a range that memory already holds keeps the relation of the memories. -/
theorem memRel_write {m : Mem} {M B : ByteArray} {o n : Nat} {src : Nat → Memory.Byte}
    (hm : MemRel m M) (hfit : n ≠ 0 → o + n ≤ M.size) (hB : B.size = n)
    (hsrc : ∀ i, i < n → (byteAt B i).toBitVec = src i) :
    MemRel (m.write o n src) (memoryWrite M o B) := by
  by_cases hz : n = 0
  · subst hz
    have hw : memoryWrite M o B = M := by simp [memoryWrite, hB]
    rw [hw]
    have hwords : (m.write o 0 src).words = m.words := by
      unfold Mem.write Mem.expand
      rw [if_pos rfl]
    have hbytes : ∀ i, (m.write o 0 src).bytes i = m.bytes i := by
      intro i
      unfold Mem.write Mem.expand
      rw [if_pos rfl]
      dsimp only
      exact if_neg (by omega)
    exact ⟨by rw [hwords]; exact hm.1, fun i => by rw [hbytes]; exact hm.2 i⟩
  have hfit' : o + B.size ≤ M.size := by rw [hB]; exact hfit hz
  refine ⟨?_, fun i => ?_⟩
  · rw [size_memoryWrite_of_fit (fun _ => hfit'), hm.1]
    unfold Mem.write Mem.expand
    simp only [hz, ite_false]
    unfold SolarTV.Memory.grow
    have hle : (m.words.ult (BitVec.ofNat 251 ((o + n + 31) / 32))) = false := by
      have h1 := hfit hz
      rw [hm.1] at h1
      have h2 : (o + n + 31) / 32 ≤ m.words.toNat := by omega
      have h3 := Nat.mod_le ((o + n + 31) / 32) (2 ^ 251)
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      omega
    simp only [hle]
    rfl
  · rw [byteAt_memoryWrite hfit']
    have hb : (m.write o n src).bytes i = if o ≤ i ∧ i < o + n then src (i - o) else m.bytes i := by
      unfold Mem.write Mem.expand
      split <;> rfl
    rw [hb, hB]
    split
    · rename_i h
      exact hsrc _ (by omega)
    · exact hm.2 i

/-- A write after growth for its range is the write. -/
theorem write_expand (m : Mem) (o n : Nat) (src : Nat → Memory.Byte) :
    (m.expand o n).write o n src = m.write o n src := by
  unfold Mem.write Mem.expand
  by_cases hz : n = 0
  · simp [hz]
  · simp only [hz, ite_false, SolarTV.Memory.grow_idempotent]

/-- The growth for a list of ranges is the growth for its first range and then for the rest,
from the size after the first. -/
theorem extendMemory_cons_expandBy {sz : Nat} (hmod : sz % 32 = 0) (r : U256 × U256)
    (rest : List (U256 × U256)) :
    (extendMemory sz (r :: rest)).expandBy = (extendMemory sz [r]).expandBy +
      (extendMemory (sz + (extendMemory sz [r]).expandBy) rest).expandBy := by
  obtain ⟨a, b⟩ := r
  simp only [extendMemory]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ite_false, ceil32_of_mod hmod]
    by_cases hg : ceil32 (a.toNat + b.toNat) ≤ sz
    · simp [hg]
    · simp only [hg, ite_false, Nat.add_zero]
      rw [show sz + (ceil32 (a.toNat + b.toNat) - sz) = ceil32 (a.toNat + b.toNat) by omega]

/-- The growth of memory for two ranges at once, as a call grows it, is the growth for the first
and then for the second. -/
theorem memRel_expand2 {m : Mem} {M : ByteArray} {o1 s1 o2 s2 : Word} (hm : MemRel m M)
    (hb1 : s1 = 0 ∨ o1.toNat + s1.toNat ≤ 2 ^ 32) (hb2 : s2 = 0 ∨ o2.toNat + s2.toNat ≤ 2 ^ 32) :
    MemRel ((m.expand o1.toNat s1.toNat).expand o2.toNat s2.toNat)
      (memoryExtend M (extendMemory M.size [(o1, s1), (o2, s2)]).expandBy) := by
  have h1 := memRel_expand hm hb1
  have h2 := memRel_expand h1 hb2
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  refine ⟨?_, fun i => ?_⟩
  · rw [← h2.1]
    simp only [size_memoryExtend, extendMemory_cons_expandBy hmod (o1, s1) [(o2, s2)]]
    omega
  · rw [byteAt_memoryExtend]
    have := h2.2 i
    rw [byteAt_memoryExtend, byteAt_memoryExtend] at this
    rw [this]

/-! ## Return data -/

/-- EthLib's return data is the oracle's for SolarTV's world. -/
def RdRel (o : Oracle) (w : List Event) (rd : ByteArray) : Prop :=
  (returndataSize o w).toNat = rd.size ∧ ∀ i, i < rd.size → returndataByte o w i = (byteAt rd i).toBitVec

/-- The oracle of a run answers the table's return data. -/
theorem rdRel_table (base : Oracle) (T : RunTable) (w : List Event) (hsz : (T.out w).size < 2 ^ 256) :
    RdRel (tableOracle base T) w (T.out w) :=
  ⟨by rw [returndataSize_table, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsz],
    fun i hi => returndataByte_table base T w i (by omega)⟩

/-- A frame starts with no return data, as the oracle of a run answers before any message. -/
theorem rdRel_initial (base : Oracle) (T : RunTable) : RdRel (tableOracle base T) [] .empty :=
  rdRel_table base T [] (by simp [out_nil])

/-! ## GAS -/

/-- **GAS** pushes EthLib's gas left after its price when the oracle answers it so. -/
theorem gas_step {o : Oracle} {call : Call} {s : State} {code : ByteArray} {msg : Message .fusaka}
    {pc g : Nat} {stack : List Word} {M : ByteArray} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x5a) (hgas : 2 ≤ g)
    (hstack : stack.length < STACK_LIMIT)
    (ho : o.env "gas" (s.world ++ [.read "gas"]) [] = BitVec.ofNat 256 (g - 2)) :
    Effect.apply o call .gas [] s =
        some (some (BitVec.ofNat 256 (g - 2)), { s with world := s.world ++ [.read "gas"] }) ∧
      Hoare .fusaka (At code msg pc stack M g st ss rd)
        (At code msg (pc + 1) (BitVec.ofNat 256 (g - 2) :: stack) M (g - 2) st ss rd) :=
  ⟨by simp [Effect.apply, ho], gas_rule hlt hbyte hgas hstack⟩

/-- GAS under the oracle of a run whose next gas is EthLib's. -/
theorem gas_step_table {base : Oracle} {T : RunTable} {call : Call} {s : State} {code : ByteArray}
    {msg : Message .fusaka} {pc g : Nat} {stack : List Word} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5a) (hgas : 2 ≤ g) (hstack : stack.length < STACK_LIMIT)
    (hT : T.gases.getD (gasReads s.world) 0 = g - 2) :
    Effect.apply (tableOracle base T) call .gas [] s =
        some (some (BitVec.ofNat 256 (g - 2)), { s with world := s.world ++ [.read "gas"] }) ∧
      Hoare .fusaka (At code msg pc stack M g st ss rd)
        (At code msg (pc + 1) (BitVec.ofNat 256 (g - 2) :: stack) M (g - 2) st ss rd) :=
  gas_step hlt hbyte hgas hstack (by rw [gas_table, hT])

/-- A GAS read keeps the return data of the oracle of a run. -/
theorem rdRel_read {base : Oracle} {T : RunTable} {w : List Event} {rd : ByteArray} (n : String)
    (h : RdRel (tableOracle base T) w rd) : RdRel (tableOracle base T) (w ++ [.read n]) rd := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · rw [returndataSize_table, rd_read, ← returndataSize_table]; exact h1
  · have hi' : i < 2 ^ 256 := by
      have := (returndataSize (tableOracle base T) w).isLt
      omega
    rw [returndataByte_table _ _ _ _ hi', rd_read, ← returndataByte_table _ _ _ _ hi']
    exact h2 i hi

/-- A log keeps the return data of the oracle of a run. -/
theorem rdRel_log {base : Oracle} {T : RunTable} {w : List Event} {rd : ByteArray}
    (t : List Word) (d : List Memory.Byte)
    (h : RdRel (tableOracle base T) w rd) : RdRel (tableOracle base T) (w ++ [.log t d]) rd := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · rw [returndataSize_table, rd_log, ← returndataSize_table]; exact h1
  · have hi' : i < 2 ^ 256 := by
      have := (returndataSize (tableOracle base T) w).isLt
      omega
    rw [returndataByte_table _ _ _ _ hi', rd_log, ← returndataByte_table _ _ _ _ hi']
    exact h2 i hi

/-! ## RETURNDATASIZE and RETURNDATACOPY -/

/-- **RETURNDATASIZE** pushes the size of EthLib's return data. -/
theorem returndatasize_step {o : Oracle} {call : Call} {s : State} {code : ByteArray}
    {msg : Message .fusaka} {pc g : Nat} {stack : List Word} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} (hr : RdRel o s.world rd)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3d) (hgas : 2 ≤ g)
    (hstack : stack.length < STACK_LIMIT) :
    Effect.apply o call .returndatasize [] s = some (some (BitVec.ofNat 256 rd.size), s) ∧
      Hoare .fusaka (At code msg pc stack M g st ss rd)
        (At code msg (pc + 1) (BitVec.ofNat 256 rd.size :: stack) M (g - 2) st ss rd) := by
  refine ⟨?_, Logic.returndatasize (by decide) hlt hbyte hgas hstack⟩
  have h1 := hr.1
  simp only [returndataSize] at h1
  simp only [Effect.apply, ← h1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- RETURNDATACOPY past the end of the return data has no SolarTV result. -/
theorem returndatacopy_past {o : Oracle} {call : Call} {s : State} {rd : ByteArray}
    {dest off size : Word} (hr : RdRel o s.world rd) (h : rd.size < off.toNat + size.toNat) :
    Effect.apply o call .returndatacopy [dest, off, size] s = none := by
  simp only [Effect.apply, hr.1, h, ite_true]

/-- **RETURNDATACOPY** within the return data writes EthLib's bytes. -/
theorem returndatacopy_step {o : Oracle} {call : Call} {s : State} {code : ByteArray}
    {msg : Message .fusaka} {pc g : Nat} {rest : List Word} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} {dest off size : Word}
    (hr : RdRel o s.world rd) (hm : MemRel s.memory M)
    (hbound : size = 0 ∨ dest.toNat + size.toNat ≤ 2 ^ 32)
    (fit : off.toNat + size.toNat ≤ rd.size) (hlt : pc < code.size) (hbyte : code[pc] = 0x3e)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory M.size [(dest, size)]).cost ≤ g) :
    ∃ m', Effect.apply o call .returndatacopy [dest, off, size] s = some (none, { s with memory := m' }) ∧
      MemRel m' (memoryWrite (memoryExtend M (extendMemory M.size [(dest, size)]).expandBy)
        dest.toNat (memoryReadBytes rd off.toNat size.toNat)) ∧
      Hoare .fusaka (At code msg pc (dest :: off :: size :: rest) M g st ss rd)
        (At code msg (pc + 1) rest
          (memoryWrite (memoryExtend M (extendMemory M.size [(dest, size)]).expandBy)
            dest.toNat (memoryReadBytes rd off.toNat size.toNat))
          (g - (3 + 3 * wordCount size.toNat + (extendMemory M.size [(dest, size)]).cost))
          st ss rd) := by
  refine ⟨s.memory.write dest.toNat size.toNat (fun i => returndataByte o s.world (off.toNat + i)),
    ?_, ?_, Logic.returndatacopy (by decide) hlt hbyte fit hgas⟩
  · have hn : ¬((returndataSize o s.world).toNat < off.toNat + size.toNat) := by rw [hr.1]; omega
    show (if (returndataSize o s.world).toNat < off.toNat + size.toNat then none else _) = _
    rw [if_neg hn]
  · have he := memRel_expand hm hbound
    rw [← write_expand]
    refine memRel_write he (fun hz => ?_) (size_memoryReadBytes fit) (fun i hi => ?_)
    · have hz' : size ≠ 0 := fun h => hz (by simp [h])
      have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
      rw [size_memoryExtend_extendMemory' hmod hz']
      have := le_ceil32 (dest.toNat + size.toNat)
      omega
    · rw [byteAt_memoryReadBytes fit, if_pos hi]
      exact (hr.2 _ (by omega)).symm

/-! ## CALLDATACOPY -/

/-- A byte of the call data, as SolarTV reads it, is EthLib's. -/
theorem calldataByte_eq (call : Call) (i : Nat) :
    calldataByte call i = (byteAt call.calldata i).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [calldataByte, BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
  rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
  unfold byteAt
  split
  · rename_i h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rfl
  · rename_i h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)]
    rfl

/-- **CALLDATACOPY** of any size writes EthLib's bytes, zero past the end of the call data. -/
theorem calldatacopy_step {o : Oracle} {call : Call} {s : State} {code : ByteArray}
    {msg : Message .fusaka} {pc g : Nat} {rest : List Word} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray} {dest off size : Word}
    (hdata : msg.data = call.calldata) (hm : MemRel s.memory M)
    (hbound : size = 0 ∨ dest.toNat + size.toNat ≤ 2 ^ 32) (hlt : pc < code.size)
    (hbyte : code[pc] = 0x37)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory M.size [(dest, size)]).cost ≤ g) :
    ∃ m', Effect.apply o call .calldatacopy [dest, off, size] s = some (none, { s with memory := m' }) ∧
      MemRel m' (memoryWrite (memoryExtend M (extendMemory M.size [(dest, size)]).expandBy)
        dest.toNat ⟨(bufferRead msg.data off.toNat size.toNat).toArray⟩) ∧
      Hoare .fusaka (At code msg pc (dest :: off :: size :: rest) M g st ss rd)
        (At code msg (pc + 1) rest
          (memoryWrite (memoryExtend M (extendMemory M.size [(dest, size)]).expandBy)
            dest.toNat ⟨(bufferRead msg.data off.toNat size.toNat).toArray⟩)
          (g - (3 + 3 * wordCount size.toNat + (extendMemory M.size [(dest, size)]).cost))
          st ss rd) := by
  refine ⟨s.memory.write dest.toNat size.toNat (fun i => calldataByte call (off.toNat + i)),
    rfl, ?_, Logic.calldatacopy hlt hbyte hgas⟩
  have he := memRel_expand hm hbound
  rw [← write_expand]
  refine memRel_write he (fun hz => ?_) (size_bufferRead _ _ _) (fun i hi => ?_)
  · have hz' : size ≠ 0 := fun h => hz (by simp [h])
    have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
    rw [size_memoryExtend_extendMemory' hmod hz']
    have := le_ceil32 (dest.toNat + size.toNat)
    omega
  · rw [byteAt_bufferRead, if_pos hi, hdata, calldataByte_eq]

/-! ## STATICCALL -/

/-- **STATICCALL in SolarTV** under an oracle that answers the call as the callee's frame `child`
ended (its success and output): the flag EthLib pushes, memory as EthLib leaves it with the
callee's output written to the output range, the return data the callee's output, and the storage
kept. -/
theorem staticcall_effect {o : Oracle} {call : Call} {s : State} {M : ByteArray}
    {gas addr inOff inSize outOff outSize : Word} {child : Evm .fusaka Nat}
    (hm : MemRel s.memory M)
    (hb1 : inSize = 0 ∨ inOff.toNat + inSize.toNat ≤ 2 ^ 32)
    (hb2 : outSize = 0 ∨ outOff.toNat + outSize.toNat ≤ 2 ^ 32)
    (hflag : callFlag o (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]) = if child.error.isNone then 1 else 0)
    (hrd : RdRel o (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]) child.output) :
    ∃ s', Effect.apply o call (.call .staticcall) [gas, addr, inOff, inSize, outOff, outSize] s =
        some (some (if child.error.isNone then 1 else 0), s') ∧
      s'.storage = s.storage ∧ s'.transient = s.transient ∧ RdRel o s'.world child.output ∧
      MemRel s'.memory (memoryWrite (memoryExtend M
          (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
        outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size))) := by
  have he := memRel_expand2 hm hb1 hb2
  refine ⟨called o .staticcall s ((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat
      outSize.toNat) outOff outSize (s.world ++ [.call .staticcall [gas, addr]
      (((s.memory.expand inOff.toNat inSize.toNat).expand outOff.toNat outSize.toNat).read
        inOff.toNat inSize.toNat) s.storage s.transient]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Effect.apply, CallKind.shape, hflag]
  · rfl
  · rfl
  · exact hrd
  · simp only [called]
    rw [hrd.1]
    refine memRel_write he (fun hz => ?_) ?_ (fun i hi => ?_)
    · have hz' : outSize ≠ 0 := fun h => hz (by simp [h])
      have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
      have := le_ceil32_add_expandBy M.size [(inOff, inSize), (outOff, outSize)] (outOff, outSize)
        (by simp) hz'
      dsimp only at this
      rw [ceil32_of_mod hmod] at this
      rw [size_memoryExtend]
      have := Nat.min_le_left outSize.toNat child.output.size
      omega
    · simp [ByteArray.size_extract]
    · rw [byteAt_extract, Nat.zero_add, if_pos (by omega)]
      exact (hrd.2 i (by omega)).symm

/-- **STATICCALL in EthLib**, at Fusaka, from EthLib's rule: under every frame that ends the
message, the caller pushes the callee's success, writes its output to the output range and keeps
its output as the return data. -/
theorem staticcall_rule {callee : Evm .fusaka Nat → Message .fusaka → Evm .fusaka Nat → Prop}
    {code : ByteArray} {msg : Message .fusaka} {pc g : Nat} {M : ByteArray}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    {asked addr inOff inSize outOff outSize : Word} {rest : List Word} {cold : Bool}
    {calleeCode : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hcode : st.getCode (st.getAccount (toAddressMasked addr)).codeHash = .ok calleeCode)
    (hdel : delegatedAddress calleeCode = none)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked addr ∉ ss.accessedAddresses) = cold)
    (hgas : (if cold then 2600 else 100) +
      (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).cost ≤ g) :
    HoareUnder .fusaka callee
      (At code msg pc (asked :: addr :: inOff :: inSize :: outOff :: outSize :: rest) M g st ss rd)
      fun after => ∃ caller m child, callee caller m child ∧ child.gas ≤ m.gas ∧
        m.isStatic = true ∧ m.value = 0 ∧
        m.data = memoryReadBytes (memoryExtend M
          (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
          inOff.toNat inSize.toNat ∧
        ∃ g' st' ss', At code msg (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
          (memoryWrite (memoryExtend M
              (extendMemory M.size [(inOff, inSize), (outOff, outSize)]).expandBy)
            outOff.toNat (child.output.extract 0 (min outSize.toNat child.output.size)))
          g' st' ss' child.output after := by
  have H := staticcallWith (fork := .fusaka) (by decide) (by decide) (callee := callee)
    (asked := asked) (rest := rest) (returnData := rd) hlt hbyte hcode (fun _ => hdel) hdepth hcold hgas
  intro bound runChild meets evm hp within
  obtain ⟨after, hr, hq⟩ := H bound runChild meets evm hp within
  refine ⟨after, hr, hq.imp_left fun ⟨caller, m, child, hc, hg, _, _, _, _, _, _, _, _, hd, hv, _,
    hs, hat⟩ => ⟨caller, m, child, hc, hg, hs, hv, hd, _, _, _, hat⟩⟩

/-- The oracle of a run answers a STATICCALL as the callee's frame ended when the table's next
entry is that frame's success and output. -/
theorem staticcall_table {base : Oracle} {T : RunTable} {w : List Event} {ops : List Word}
    {input : List Memory.Byte} {stor tr : Word → Word} {child : Evm .fusaka Nat}
    (hok : T.oks.getD (sent w) false = child.error.isNone)
    (hout : T.outs.getD (sent w) .empty = child.output) (hsz : child.output.size < 2 ^ 256) :
    callFlag (tableOracle base T) (w ++ [.call .staticcall ops input stor tr]) =
        (if child.error.isNone then 1 else 0) ∧
      RdRel (tableOracle base T) (w ++ [.call .staticcall ops input stor tr]) child.output := by
  refine ⟨by rw [callFlag_table, hok], ?_⟩
  have h := rdRel_table base T (w ++ [.call .staticcall ops input stor tr])
    (by rw [out_call, hout]; exact hsz)
  rwa [out_call, hout] at h

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.staticcall_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_effect

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.staticcall_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_rule

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.returndatacopy_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms returndatacopy_step

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.calldatacopy_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calldatacopy_step

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.gas_step_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gas_step_table

end SolidCore.Refinement.Solar.AssembleEffects
