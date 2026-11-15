import SolidCore.Solidity.Shared.Word

/-!
# Lane F: `clzWord` is `BitVec.clz`

SolidCore's `Shared.clzWord` counts leading zeros of a 256-bit word with a 256-step scan
(`clzWordAux 256 255`). Lean core's `BitVec.clz` (Init/Data/BitVec/Basic.lean, `clzAuxRec`)
scans the same bits in the same order. `clzWord_eq_clz` says the two agree on every `Nat`,
zero included (`clzWord 0 = 256`, `BitVec.clz 0#256 = 256#256`), so a proof can use core's
`clz` lemmas (`clz_le`, `clz_eq_iff_eq_zero`, `clz_eq_zero_iff`, ...) instead of unfolding the
scan. Only core imports besides the module under test.
-/

namespace Verify.Eval.F

open SolidCore.Solidity.Shared

/-- A single-bit mask is nonzero exactly when that bit is set. -/
theorem land_two_pow_pos (x n : Nat) : 0 < Nat.land x (2 ^ n) ↔ x.testBit n = true := by
  show 0 < x &&& 2 ^ n ↔ _
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [Nat.testBit_and, Nat.testBit_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.2 ▸ hi.1
  · intro h
    have : (x &&& 2 ^ n).testBit n = true := by simp [h]
    exact Nat.lt_of_lt_of_le (Nat.two_pow_pos n) (Nat.ge_two_pow_of_testBit this)

theorem testBit_norm {v n : Nat} (hn : n < 256) : (norm v).testBit n = v.testBit n := by
  show (v % 2 ^ 256).testBit n = _
  rw [Nat.testBit_mod_two_pow]; simp [hn]

/-- Step by step, the scan below bit `n` is core's `clzAuxRec` at `n`. -/
theorem clzWordAux_eq_clzAuxRec (v : Nat) :
    ∀ n, n < 256 → clzWordAux (n + 1) n v = ((BitVec.ofNat 256 v).clzAuxRec n).toNat
  | 0, _ => by
    simp only [clzWordAux, BitVec.clzAuxRec_zero, BitVec.getLsbD_ofNat,
      land_two_pow_pos, testBit_norm (show 0 < 256 by decide)]
    cases v.testBit 0 <;> rfl
  | n + 1, hn => by
    have hn' : n + 1 < 256 := hn
    rw [clzWordAux, Nat.add_sub_cancel, clzWordAux_eq_clzAuxRec v n (by omega)]
    simp only [BitVec.clzAuxRec_succ, BitVec.getLsbD_ofNat, land_two_pow_pos, testBit_norm hn]
    cases v.testBit (n + 1) <;> simp [hn', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le 254 n) (by decide))).symm

/-- **The bridge.** `clzWord` is core's `BitVec.clz` on the word's bit vector. -/
theorem clzWord_eq_clz (v : Nat) : clzWord v = (BitVec.ofNat 256 v).clz.toNat := by
  unfold clzWord
  rw [clzWordAux_eq_clzAuxRec v 255 (by decide)]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

/-- The same bridge read from a `BitVec`. -/
theorem clzWord_toNat (x : BitVec 256) : clzWord x.toNat = x.clz.toNat := by
  rw [clzWord_eq_clz, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The zero case, `zero256`: `clzWord` is 256 exactly on words that are zero mod 2^256. -/
theorem clzWord_eq_256_iff (v : Nat) : clzWord v = 256 ↔ v % 2 ^ 256 = 0 := by
  rw [clzWord_eq_clz]
  have h := BitVec.clz_eq_iff_eq_zero (x := BitVec.ofNat 256 v)
  constructor
  · intro hc
    have : (BitVec.ofNat 256 v).clz = (256 : Nat) := BitVec.eq_of_toNat_eq (by simpa using hc)
    have h0 := congrArg BitVec.toNat (h.mp this)
    simpa using h0
  · intro hv
    have : BitVec.ofNat 256 v = 0#256 := BitVec.eq_of_toNat_eq (by simpa using hv)
    rw [h.mpr this]; rfl

theorem clzWord_zero : clzWord 0 = 256 := (clzWord_eq_256_iff 0).mpr rfl

theorem clzWord_le (v : Nat) : clzWord v ≤ 256 := by
  rw [clzWord_eq_clz]
  have := BitVec.clz_le (x := BitVec.ofNat 256 v)
  rw [BitVec.le_def] at this
  simpa using this

/-! ## Fixtures (new). The old proofs are in ClzOld.lean. -/

/-- The top bit set gives no leading zeros, for every such word: core's `clz_eq_zero_iff`. -/
theorem fixture_clz_top (v : Nat) (h : 2 ^ 255 ≤ v % 2 ^ 256) : clzWord v = 0 := by
  rw [clzWord_eq_clz]
  exact (BitVec.clz_eq_zero_iff (by decide)).mpr (by simpa using h)

/-- A concrete word: `2^200 + 7` has 55 leading zeros. -/
theorem fixture_clz_concrete : clzWord (2 ^ 200 + 7) = 55 := by decide

end Verify.Eval.F

#print axioms Verify.Eval.F.clzWord_eq_clz
