import Std.Data.HashMap

/-!
# HashMap bucket indices the kernel can evaluate

`Std.DHashMap.Internal.mkIdx` computes a bucket index as a `USize`, and a `USize`'s width
is `System.Platform.numBits`, which reads the opaque `System.Platform.getNumBits`. So
the kernel cannot evaluate `mkIdx` for a nonzero hash, and any `Std.HashMap` with an entry
in a bucket other than the first is stuck under kernel evaluation. That includes SolidCore's
storage after a constructor that writes two or more slots.

`mkIdxNat` is the same index computed on `Nat` when the bucket count is below `2 ^ 32`
(the least `USize.size`, so the mask never reaches the bits the platform width cuts), built
with `USize.ofNatLT`, whose `toNat` reduces structurally whatever the width is.
`mkIdx_eq` proves the two functions equal, for both platform widths, so a check may evaluate
`mkIdxNat` in place of `mkIdx` (`kernel_rfl … using mkIdx_eq`). No axiom beyond Lean's
standard three, and nothing about the platform is assumed.
-/

namespace Verify.Lifecycle

open Std.DHashMap.Internal

theorem mask_lt {sz : Nat} (x : Nat) (h : 0 < sz) (hs : sz < 2 ^ 32) :
    x &&& (sz - 1) < USize.size :=
  Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_lt_of_le (by omega) USize.le_size)

theorem mask_lt_sz {sz : Nat} (x : Nat) (h : 0 < sz) : x &&& (sz - 1) < sz :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- `mkIdx`, computed on `Nat` for fewer than `2 ^ 32` buckets. -/
def mkIdxNat (sz : Nat) (h : 0 < sz) (hash : UInt64) : { u : USize // u.toNat < sz } :=
  if hs : sz < 2 ^ 32 then
    ⟨USize.ofNatLT ((scrambleHash hash).toNat &&& (sz - 1)) (mask_lt _ h hs), mask_lt_sz _ h⟩
  else mkIdx sz h hash

theorem mkIdx_eq : mkIdx = mkIdxNat := by
  funext sz h hash
  unfold mkIdxNat
  split
  · next hs =>
    apply Subtype.ext
    apply USize.toNat_inj.mp
    have hsz : sz < USize.size := Nat.lt_of_lt_of_le hs USize.le_size
    have hm : sz - 1 < 2 ^ System.Platform.numBits := by
      have e : USize.size = 2 ^ System.Platform.numBits := rfl
      omega
    unfold mkIdx
    simp only [USize.toNat_and, UInt64.toNat_toUSize, USize.toNat_ofNatLT]
    rw [USize.toNat_sub_of_le _ _ (by
      rw [USize.le_iff_toNat_le, USize.toNat_ofNat_of_lt' hsz]; simp; omega),
      USize.toNat_ofNat_of_lt' hsz]
    simp only [USize.toNat_one]
    rw [← Nat.mod_eq_of_lt hm, ← Nat.and_mod_two_pow, Nat.mod_eq_of_lt hm,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hm)]
  · rfl

end Verify.Lifecycle
