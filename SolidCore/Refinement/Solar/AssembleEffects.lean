import SolidCore.Refinement.Solar.RunOracle
import EthLib.Execution.Proofs.Evm.Logic.Copy
import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.Known

/-!
# EVM IR to bytecode: the instructions of a run's oracle

The relations the simulations from EVM IR to bytecode keep across instructions that read what the oracle of
a run answers or copy a range of dynamic size, used by the per-instruction steps of
`AssembleCall`, `AssembleCallSeg`, `AssembleDynCopy` and their kin:

* `MemRel` after a write of a range (`memRel_write`) and after the growth of memory for two ranges
  at once, as a call grows it (`memRel_expand2`).
* `RdRel o w rd`: EthLib's return data `rd` is the oracle's for SolarTV's world `w`. The oracle of a
  run meets it for the table's return data (`rdRel_table`); a log or a GAS read keeps it.
* A byte of the call data, as SolarTV reads it, is EthLib's (`calldataByte_eq`).
* STATICCALL in SolarTV (`staticcall_effect`): under an oracle that answers the call's success and
  output as the callee ended, the flag, memory with the callee's output written, the return data
  and the storage are EthLib's.
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

/-- An event that keeps the table's return data keeps the return data of the oracle of a run. -/
theorem rdRel_append {base : Oracle} {T : RunTable} {w : List Event} {rd : ByteArray} {e : Event}
    (he : T.out (w ++ [e]) = T.out w) (h : RdRel (tableOracle base T) w rd) :
    RdRel (tableOracle base T) (w ++ [e]) rd := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · rw [returndataSize_table, he, ← returndataSize_table]; exact h1
  · have hi' : i < 2 ^ 256 := by
      have := (returndataSize (tableOracle base T) w).isLt
      omega
    rw [returndataByte_table _ _ _ _ hi', he, ← returndataByte_table _ _ _ _ hi']
    exact h2 i hi

/-- A GAS read keeps the return data of the oracle of a run. -/
theorem rdRel_read {base : Oracle} {T : RunTable} {w : List Event} {rd : ByteArray} (n : String)
    (h : RdRel (tableOracle base T) w rd) : RdRel (tableOracle base T) (w ++ [.read n]) rd :=
  rdRel_append (rd_read T w n) h

/-- A log keeps the return data of the oracle of a run. -/
theorem rdRel_log {base : Oracle} {T : RunTable} {w : List Event} {rd : ByteArray}
    (t : List Word) (d : List Memory.Byte)
    (h : RdRel (tableOracle base T) w rd) : RdRel (tableOracle base T) (w ++ [.log t d]) rd :=
  rdRel_append (rd_log T w t d) h

/-! ## Call data -/

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

/-- info: 'SolidCore.Refinement.Solar.AssembleEffects.staticcall_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms staticcall_effect

end SolidCore.Refinement.Solar.AssembleEffects
