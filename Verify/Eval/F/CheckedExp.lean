import SolidCore.Solidity.Interpreter

/-!
# Lane F: SolidCore's checked `**` through `Nat.powMod`

Solidity's checked `**` is `SolidCore.Solidity.Source.checkedExp`
(SolidCore/Solidity/Interpreter.lean:6703): it panics with 0x11 when `natPowCapped b e 2^256`
saturates, and otherwise returns `natPowMod b e 2^256`, both by squaring with 257 fuel
(`expBySquaring`, Interpreter.lean:6674). This file proves, for every exponent below `2^257`
(every word):

* `natPowMod b e m = Nat.powMod b e m` (core's square-and-multiply), so `= b ^ e % m`;
* `natPowCapped b e cap = min (b ^ e) cap` for `0 < cap`;
* `checkedExp_eq`: the overflow-panic point is exactly `2^256 ≤ b ^ e` (the checked semantics is
  kept, now stated on the true power), and the value is `Nat.powMod`;
* `checkedExp_unchecked`: unchecked `**` is core's `BitVec` power on `BitVec.ofNat 256 b`, which
  Power.lean bridges to `SolarTV.Word.power`.

Core lemmas only (no Mathlib).
-/

namespace Verify.Eval.F

open SolidCore.Solidity.Source

set_option linter.deprecated false

/-- The value of a bit-vector power (core v4.35 has no `BitVec.toNat_pow`). -/
theorem bv_toNat_pow' {w : Nat} (x : BitVec w) (n : Nat) :
    (x ^ n).toNat = x.toNat ^ n % 2 ^ w := by
  induction n with
  | zero => simp [BitVec.pow_zero]
  | succ n ih => rw [BitVec.pow_succ, BitVec.toNat_mul, ih, Nat.pow_succ, Nat.mod_mul_mod]

theorem expBySquaring_e_zero (f : Nat → Nat → Nat) :
    ∀ fuel acc b, expBySquaring f fuel acc b 0 = acc
  | 0, _, _ => rfl
  | _ + 1, _, _ => by simp [expBySquaring]

/-- A reducing multiplication `g (x * y)` passes `g` through either factor. -/
theorem g_pow {g : Nat → Nat} (h2 : ∀ a b, g (a * g b) = g (a * b)) :
    ∀ k x y, g (x * g y ^ k) = g (x * y ^ k)
  | 0, x, y => by simp
  | k + 1, x, y => by
    rw [Nat.pow_succ, ← Nat.mul_assoc, h2, Nat.mul_right_comm, g_pow h2 k (x * y) y,
      Nat.mul_assoc, ← Nat.pow_succ']

/-- Exponentiation by squaring with a reducing multiplication `g (x * y)` computes
`g (acc * b ^ e)`, when `g` passes through either factor and the fuel covers `e`. -/
theorem expBySquaring_eq (g : Nat → Nat) (h1 : ∀ a b, g (g a * b) = g (a * b))
    (h2 : ∀ a b, g (a * g b) = g (a * b)) :
    ∀ fuel acc b e, e < 2 ^ fuel → e ≠ 0 →
      expBySquaring (fun x y => g (x * y)) fuel acc b e = g (acc * b ^ e)
  | 0, _, _, e, he, hne => by simp at he; omega
  | fuel + 1, acc, b, e, he, hne => by
    rw [expBySquaring, if_neg hne]
    simp only []
    by_cases h0 : e / 2 = 0
    · have : e = 1 := by omega
      subst this
      simp [expBySquaring_e_zero]
    · rw [if_neg h0, expBySquaring_eq g h1 h2 fuel _ _ (e / 2)
        (by rw [Nat.pow_succ] at he; omega) h0, g_pow h2]
      have hsq : b * b = b ^ 2 := (Nat.pow_two b).symm
      rw [hsq, ← Nat.pow_mul]
      split
      · rw [h1, Nat.mul_assoc, ← Nat.pow_succ']
        have : 2 * (e / 2) + 1 = e := by omega
        rw [Nat.succ_eq_add_one, this]
      · have : 2 * (e / 2) = e := by omega
        rw [this]

theorem natPowMod_eq_powMod (b e m : Nat) (he : e < 2 ^ 257) :
    natPowMod b e m = Nat.powMod b e m := by
  rw [Nat.powMod_def]
  unfold natPowMod expFuel
  by_cases h0 : e = 0
  · subst h0; simp [expBySquaring_e_zero]
  · rw [expBySquaring_eq (· % m) (fun a b => Nat.mod_mul_mod a b m)
      (fun a b => Nat.mul_mod_mod a b m) 257 _ _ e he h0]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod, Nat.one_mul]

theorem min_mul_left (a b c : Nat) : min (min a c * b) c = min (a * b) c := by
  by_cases hac : a ≤ c
  · rw [Nat.min_eq_left hac]
  · rw [Nat.min_eq_right (a := a) (b := c) (by omega)]
    cases b with
    | zero => simp
    | succ b =>
      have h1 : c ≤ c * (b + 1) := Nat.le_mul_of_pos_right c (by omega)
      have h2 : c ≤ a * (b + 1) :=
        Nat.le_trans (by omega) (Nat.le_mul_of_pos_right a (by omega))
      rw [Nat.min_eq_right h1, Nat.min_eq_right h2]

theorem natPowCapped_eq (b e cap : Nat) (he : e < 2 ^ 257) (hcap : 0 < cap) :
    natPowCapped b e cap = min (b ^ e) cap := by
  unfold natPowCapped expFuel
  by_cases h0 : e = 0
  · subst h0; simp [expBySquaring_e_zero]; omega
  · rw [expBySquaring_eq (min · cap) (fun a b => min_mul_left a b cap)
      (fun a b => by rw [Nat.mul_comm, min_mul_left, Nat.mul_comm]) 257 _ _ e he h0, Nat.one_mul]

theorem wordModulus_eq : wordModulus = 2 ^ 256 := rfl

theorem norm_lt (x : Nat) : SolidCore.Solidity.Shared.norm x < 2 ^ 257 :=
  Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos 256))
    (show 2 ^ 256 < 2 ^ 257 from Nat.pow_lt_pow_right (by decide) (by decide))

/-- **Checked `**`, bridged.** It panics exactly when the true power reaches `2^256`, and
otherwise returns `Nat.powMod`. -/
theorem checkedExp_eq (checked : Bool) (base exponent : Word) :
    checkedExp checked base exponent =
      let b := SolidCore.Solidity.Shared.norm base
      let e := SolidCore.Solidity.Shared.norm exponent
      if checked && decide (2 ^ 256 ≤ b ^ e) then .error RevertData.overflow
      else .ok (Nat.powMod b e (2 ^ 256)) := by
  unfold checkedExp
  simp only [wordModulus_eq, natPowCapped_eq _ _ _ (norm_lt _) (Nat.two_pow_pos 256),
    natPowMod_eq_powMod _ _ _ (norm_lt _), Nat.le_min, Nat.le_refl, and_true]
  congr 1
  simp only [normWord, SolidCore.Solidity.Shared.norm, SolidCore.Solidity.Shared.wordModulus,
    EvmYul.UInt256.size]
  rw [Nat.powMod_def]
  simp only [Nat.reducePow, Nat.mod_mod]

/-- Unchecked `**` is core's `BitVec` power (and so `SolarTV.Word.power`, by `power_eq_pow`). -/
theorem checkedExp_unchecked (base exponent : Word) :
    checkedExp false base exponent =
      .ok ((BitVec.ofNat 256 base) ^ SolidCore.Solidity.Shared.norm exponent).toNat := by
  rw [checkedExp_eq]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  congr 1
  rw [bv_toNat_pow', Nat.powMod_def, BitVec.toNat_ofNat]
  rfl

/-! ## Fixture: a symbolic exponent (new). The old attempt is in CheckedExpOld.lean. -/

/-- `1 ** e` never panics and is 1, for every exponent: no unfolding of the 257-step loop. -/
theorem fixture_one_pow (checked : Bool) (e : Word) : checkedExp checked 1 e = .ok 1 := by
  rw [checkedExp_eq]
  simp [SolidCore.Solidity.Shared.norm, SolidCore.Solidity.Shared.wordModulus,
    EvmYul.UInt256.size, Nat.powMod_def]

/-- `b ** 2` with `b < 2^128` does not panic and is `b * b`. -/
theorem fixture_sq (b : Word) (hb : b < 2 ^ 128) : checkedExp true b 2 = .ok (b * b) := by
  have hb' : b < 2 ^ 256 := Nat.lt_trans hb (by decide)
  have hsq : b * b < 2 ^ 256 := by
    have := Nat.mul_lt_mul'' hb hb
    rwa [← Nat.pow_add] at this
  rw [checkedExp_eq]
  simp only [SolidCore.Solidity.Shared.norm, SolidCore.Solidity.Shared.wordModulus,
    EvmYul.UInt256.size, Nat.powMod_def, Nat.pow_two, Nat.reducePow, Nat.reduceMod] at *
  simp [Nat.mod_eq_of_lt hb', Nat.not_le.mpr hsq, Nat.mod_eq_of_lt hsq]

/-- Overflow decided on the true power by monotonicity, for every exponent from 256 up: no
evaluation of the loop, and no evaluation of `3 ^ e`. -/
theorem fixture_overflow (e : Word) (h1 : 256 ≤ e) (h2 : e < 2 ^ 256) :
    checkedExp true 3 e = .error RevertData.overflow := by
  have hle : 2 ^ 256 ≤ 3 ^ e :=
    Nat.le_trans (Nat.pow_le_pow_left (by decide) 256) (Nat.pow_le_pow_right (by decide) h1)
  have h3 : SolidCore.Solidity.Shared.norm 3 = 3 := rfl
  have he : SolidCore.Solidity.Shared.norm e = e := by
    show e % 2 ^ 256 = e
    exact Nat.mod_eq_of_lt h2
  rw [checkedExp_eq]
  simp only [h3, he, hle, decide_true, Bool.true_and, if_true]

end Verify.Eval.F

/-- info: 'Verify.Eval.F.checkedExp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.checkedExp_eq
/-- info: 'Verify.Eval.F.checkedExp_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.checkedExp_unchecked
/-- info: 'Verify.Eval.F.fixture_one_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Verify.Eval.F.fixture_one_pow
