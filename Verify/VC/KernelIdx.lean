import Std

/-!
# Hash map buckets the kernel can compute

`Std.HashMap` picks a key's bucket with `mkIdx`, a `USize` computation. The width of `USize` is
`System.Platform.numBits`, which the kernel cannot reduce, so no lookup or insert, and nothing that
runs the constructor of a contract that writes storage, reduces by conversion alone. `mkIdxK`
computes the same index on `Nat` for every table below `2 ^ 32` buckets, where the mask fits either
platform's word, and falls back to `mkIdx` otherwise. `mkIdx_eq` proves the two equal, so
`kernel_rfl … using mkIdx_eq` evaluates hash maps in the kernel without assuming a platform.
-/

namespace SolidCore.Verify.VC

open Std.DHashMap.Internal

/-- Either platform's `USize` holds every `Nat` below `2 ^ 32`. -/
theorem usize_size_ge : 2 ^ 32 ≤ USize.size := by
  rcases USize.size_eq with h | h <;> rw [h] <;> decide

/-- `mkIdx` on `Nat` below `2 ^ 32` buckets, where its mask does not depend on the word width. -/
def mkIdxK (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  if hs : sz < 2 ^ 32 then
    ⟨USize.ofNatLT ((scrambleHash hash).toNat &&& (sz - 1))
        (Nat.lt_of_le_of_lt Nat.and_le_right (by have := usize_size_ge; omega)),
      by
        show (scrambleHash hash).toNat &&& (sz - 1) < sz
        exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)⟩
  else mkIdx sz h hash

/-- `mkIdxK` is `mkIdx`, whatever `System.Platform.numBits` is. -/
theorem mkIdx_eq : @mkIdx = @mkIdxK := by
  funext sz h hash
  unfold mkIdxK
  split
  · next hs =>
    apply Subtype.ext
    apply USize.toNat_inj.mp
    have hsz := usize_size_ge
    unfold mkIdx
    simp only [USize.toNat_and, USize.toNat_ofNatLT, UInt64.toNat_toUSize]
    rw [USize.toNat_sub_of_le, USize.toNat_ofNat_of_lt' (by omega)]
    · simp only [USize.toNat_one]
      have hm : sz - 1 < 2 ^ System.Platform.numBits := by
        have : USize.size = 2 ^ System.Platform.numBits := rfl
        omega
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
      by_cases hi : i < System.Platform.numBits
      · simp [hi]
      · have : sz - 1 < 2 ^ i :=
          Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
        simp [hi, Nat.testBit_lt_two_pow this]
    · simp [USize.le_iff_toNat_le, USize.toNat_ofNat_of_lt' (show sz < USize.size by omega)]; omega
  · rfl

end SolidCore.Verify.VC
