import SolidCore.Refinement.Solar.AssembleLoopSim

/-!
# Memory that a budget of gas pays for

SolarTV counts the active words of memory in `BitVec 251`, EthLib in a `Nat`. Memory whose price
`3 w + w ^ 2 / 512` is within a budget below `2 ^ 300` has fewer than `2 ^ 155` words
(`words_lt_of_cost`), so growth that a run pays for never wraps in SolarTV, and SolarTV's memory
agrees with EthLib's after it at any offset (`memRel_expandW`, `memRel_storeW`: the lemmas of
`Assemble` without the `2 ^ 32` bound of constant offsets).
-/

namespace SolidCore.Refinement.Solar.AssembleLoop

open SolarTV SolarTV.Machine
open SolidCore.Refinement.Solar.Assemble
open SolarTV.Assembly
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

set_option exponentiation.threshold 600 in
/-- A square below \`2 ^ 502\` has its root below \`2 ^ 251\`. -/
theorem lt_of_mul_self_lt {w : Nat} (h : w * w < 2 ^ 502) : w < 2 ^ 251 := by
  refine Nat.lt_of_not_le fun hw => ?_
  have hsq := Nat.mul_le_mul hw hw
  have e : (2 : Nat) ^ 251 * 2 ^ 251 = 2 ^ 502 := by rw [← Nat.pow_add]
  omega

/-- **Memory a budget below \`2 ^ 300\` pays for has fewer than \`2 ^ 251\` words**, so SolarTV's count
of words does not wrap. -/
theorem words_lt_of_cost {n B : Nat} (h : memoryGasCost n ≤ B) (hB : B < 2 ^ 300) :
    (n + 31) / 32 < 2 ^ 251 := by
  have hw := wordCount_mul_self_le h
  have e : wordCount n = (n + 31) / 32 := by
    unfold wordCount WORD_BYTES
    rw [ceil32_eq]
    omega
  rw [e] at hw
  apply lt_of_mul_self_lt
  generalize (n + 31) / 32 * ((n + 31) / 32) = sq at hw ⊢
  omega

/-- Memory a budget below `2 ^ 256` pays for is at most `2 ^ 140` bytes. -/
theorem size_le_of_cost {n B : Nat} (h : memoryGasCost n ≤ B) (hB : B < 2 ^ 256) (hmod : n % 32 = 0) :
    n ≤ 2 ^ 140 := by
  have hw := wordCount_mul_self_le h
  have e : wordCount n = (n + 31) / 32 := by
    unfold wordCount WORD_BYTES
    rw [ceil32_eq]
    omega
  rw [e] at hw
  have hlt : (n + 31) / 32 < 2 ^ 135 := by
    refine Nat.lt_of_not_le fun hw' => ?_
    have hsq := Nat.mul_le_mul hw' hw'
    have e2 : (2 : Nat) ^ 135 * 2 ^ 135 = 2 ^ 270 := by rw [← Nat.pow_add]
    generalize (n + 31) / 32 * ((n + 31) / 32) = sq at hw hsq
    omega
  omega

/-! ## SolarTV's memory and EthLib's at any range SolarTV holds -/

open SolarTV.Machine in
/-- \`Assemble.memRel_expand\` for every range whose words SolarTV holds. -/
theorem memRel_expandW {m : Mem} {M : ByteArray} {o sz : Word} (hm : MemRel m M)
    (hbound : sz = 0 ∨ (o.toNat + sz.toNat + 31) / 32 < 2 ^ 251) :
    MemRel (m.expand o.toNat sz.toNat) (memoryExtend M (extendMemory M.size [(o, sz)]).expandBy) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hb : (m.expand o.toNat sz.toNat).bytes = m.bytes := by unfold Mem.expand; split <;> rfl
  refine ⟨?_, fun i => by rw [byteAt_memoryExtend, hb]; exact hm.2 i⟩
  by_cases hz : sz = 0
  · subst hz
    rw [extendMemory_zero', memoryExtend_zero]
    simpa [Mem.expand] using hm.1
  · have hlt := hbound.resolve_left hz
    rw [size_memoryExtend_extendMemory' hmod hz, hm.1, ceil32_eq]
    have hz' : sz.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq (by simpa using h))
    unfold Mem.expand SolarTV.Memory.grow
    simp only [hz', ite_false]
    split
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      omega

open SolarTV.Machine in
/-- \`Assemble.memRel_store\` for every offset whose word SolarTV holds. -/
theorem memRel_storeW {m : Mem} {M : ByteArray} {o v : Word} (hm : MemRel m M)
    (hlt : (o.toNat + 32 + 31) / 32 < 2 ^ 251) :
    MemRel (m.store o.toNat v)
      (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat (wordBytes v)) ∧
    (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
      (wordBytes v)).size = max M.size (ceil32 (o.toNat + 32)) := by
  have hmod : M.size % 32 = 0 := by rw [hm.1]; omega
  have hext := size_memoryExtend_extendMemory' (memory := M) (start := o) (length := 32) hmod
    (by decide)
  have h32 : (32 : U256).toNat = 32 := rfl
  rw [h32] at hext
  have hfit : o.toNat + (wordBytes v).size ≤
      (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy).size := by
    rw [size_wordBytes, hext]
    have := le_ceil32 (o.toNat + 32)
    omega
  have hsize : (memoryWrite (memoryExtend M (extendMemory M.size [(o, 32)]).expandBy) o.toNat
      (wordBytes v)).size = max M.size (ceil32 (o.toNat + 32)) := by
    rw [size_memoryWrite_of_fit (fun _ => hfit), hext]
  refine ⟨⟨?_, fun i => ?_⟩, hsize⟩
  · rw [hsize, hm.1, ceil32_eq]
    unfold Mem.store Mem.expand SolarTV.Memory.grow
    simp only [show (32 = 0) = False from by decide, ite_false]
    split
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      omega
    · rename_i h
      rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at h
      omega
  · rw [byteAt_memoryWrite hfit, byteAt_memoryExtend, size_wordBytes]
    have hb : (m.store o.toNat v).bytes i =
        if o.toNat ≤ i ∧ i < o.toNat + 32 then SolarTV.Memory.byte v (i - o.toNat) else m.bytes i := by
      unfold Mem.store Mem.expand
      simp only [show (32 = 0) = False from by decide, ite_false]
    rw [hb]
    split
    · rename_i h
      exact byteAt_wordBytes v _ (by omega)
    · exact hm.2 i

end SolidCore.Refinement.Solar.AssembleLoop
