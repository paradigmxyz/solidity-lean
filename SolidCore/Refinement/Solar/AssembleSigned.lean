import EthLib.Execution.Evm.Instructions.Arithmetic
import EthLib.Execution.Evm.Instructions.Bitwise
import EthLib.Execution.Evm.Instructions.StackOnly
import EthLib.Base.Proofs.U256
import EvmRules.Word
import SolarTV.Word

/-!
# SDIV, SMOD, SAR, SIGNEXTEND and EXP: EthLib's rules are the EVM IR's word operations

The assembly checker (`Assemble.check` and the checkers built on its step) runs a stack
operation of the final EVM IR at its opcode with EthLib's own rule for that opcode and shows
that EthLib computes the word SolarTV's EVM IR semantics computes, `EvmRules.Evm`'s operation
(`Assemble.stack_rule`). This file gives that equality for the signed operations and EXP:

* `sdiv_agree`: EthLib's SDIV, written over two's-complement integers (the quotient rounded
  toward zero, `-2^255 / -1 = -2^255`, and 0 for a divisor of 0), is `BitVec.sdiv`;
* `smod_agree`: EthLib's SMOD (the remainder with the dividend's sign, 0 for a divisor of 0) is
  `BitVec.srem` guarded by the divisor;
* `sar_agree`: EthLib's SAR (an integer shift, which rounds toward negative infinity, and the
  sign fill from 256 bits on) is `BitVec.sshiftRight'` guarded by the shift;
* `signextend_agree`: EthLib's SIGNEXTEND (the low `b + 1` bytes read as a signed integer,
  widened, and the word unchanged from `b = 31` on) is `EvmRules.Evm.signextend`, one
  `BitVec.signExtend` per byte count;
* `exp_agree`: EthLib's EXP (square-and-multiply modulo `2^256`) is SolarTV's `Word.power`
  (square-and-multiply on words), and `exp_cost_le` bounds its price at Fusaka by 1610 (10 and
  50 for each of at most 32 bytes of exponent).

Every proof goes through `BitVec.toInt` or `BitVec.toNat` and Lean's own `BitVec` lemmas; no
solver and no evaluation of symbolic words.
-/

namespace SolidCore.Refinement.Solar.AssembleSigned

open EthLib.Base EthLib.Execution.Evm GasCosts

abbrev Word := EvmRules.Word

/-! ## Integer division and remainder -/

/-- `tdiv` as the sign of the product times the quotient of the absolute values, the form of
the execution specification EthLib transcribes. -/
theorem natAbs_succ (k : Nat) : ((k : Int) + 1).natAbs = k + 1 := by
  have := Int.natAbs_natCast (k + 1)
  simpa using this

theorem tdiv_eq_sign_mul (d v : Int) :
    d.tdiv v = (d * v).sign * ((d.natAbs / v.natAbs : Nat) : Int) := by
  rw [Int.sign_mul]
  rcases d with (_ | m) | m <;> rcases v with (_ | n) | n <;> simp [Int.tdiv, natAbs_succ]

/-- `tmod` as the sign of the dividend times the remainder of the absolute values. -/
theorem tmod_eq_sign_mul (d v : Int) :
    d.tmod v = d.sign * ((d.natAbs % v.natAbs : Nat) : Int) := by
  rcases d with (_ | m) | m <;> rcases v with (_ | n) | n <;> simp [Int.tmod, natAbs_succ]

theorem toInt_eq_zero {x : Word} : x.toInt = 0 ↔ x = 0 := by
  constructor
  · intro h; rw [← BitVec.toInt_inj]; simpa using h
  · intro h; subst h; simp

/-- EthLib's SDIV is `BitVec.sdiv`, which `EvmRules.Evm.sdiv` is. -/
theorem sdiv_agree (x y : Word) : sdiv x y = EvmRules.Evm.sdiv x y := by
  unfold sdiv EvmRules.Evm.sdiv
  simp only [U256.toSigned_eq_toInt, U256.fromSigned]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv]
  by_cases h0 : y.toInt = 0
  · rw [if_pos h0, h0]
    simp
  · rw [if_neg h0]
    by_cases hm : x.toInt = -2 ^ 255 ∧ y.toInt = -1
    · rw [if_pos hm, hm.1, hm.2, BitVec.toInt_ofInt]
      decide
    · rw [if_neg hm, BitVec.toInt_ofInt, tdiv_eq_sign_mul]

/-- EthLib's SMOD is `BitVec.srem` guarded by the divisor, which `EvmRules.Evm.smod` is. -/
theorem smod_agree (x y : Word) : smod x y = EvmRules.Evm.smod x y := by
  unfold smod EvmRules.Evm.smod
  simp only [U256.toSigned_eq_toInt, U256.fromSigned]
  by_cases h0 : y = 0
  · subst h0
    simp
  · have h0' : y.toInt ≠ 0 := fun h => h0 (toInt_eq_zero.mp h)
    have hb : (y == 0) = false := by simpa using h0
    rw [if_neg h0', hb, cond_false, ← tmod_eq_sign_mul, ← BitVec.toInt_srem, BitVec.ofInt_toInt]

/-! ## Arithmetic shift -/

/-- EthLib's SAR is `BitVec.sshiftRight'` below 256 bits of shift and the sign fill from there,
which `EvmRules.Evm.sar` is. -/
theorem sar_agree (x y : Word) : bitwiseSar x y = EvmRules.Evm.sar x y := by
  unfold bitwiseSar EvmRules.Evm.sar
  simp only [U256.toSigned_eq_toInt, U256.fromSigned]
  by_cases hs : x.toNat < 256
  · have hu : x.ult (256 : Word) = true := by simp [BitVec.ult, hs]
    rw [if_pos hs, hu, cond_true]
    rfl
  · have hu : x.ult (256 : Word) = false := by simp [BitVec.ult]; omega
    rw [if_neg hs, hu, cond_false, BitVec.msb_eq_toInt]
    by_cases hn : 0 ≤ y.toInt
    · rw [if_pos hn]
      simp [show ¬ y.toInt < 0 by omega]
    · rw [if_neg hn]
      simp [show y.toInt < 0 by omega, BitVec.neg_one_eq_allOnes]

/-! ## Sign extension -/

/-- The low `w` bits of a word, sign-extended to 256 bits, as EthLib writes it: the low bits
when their top bit is clear, and with every bit above them set otherwise. -/
theorem signExtend_low (v : Word) (w : Nat) (hw' : w ≤ 256) :
    (v.setWidth w).signExtend 256 =
      if v.toNat % 2 ^ w < 2 ^ (w - 1) then BitVec.ofNat 256 (v.toNat % 2 ^ w)
      else BitVec.ofNat 256 (2 ^ 256 - 2 ^ w + v.toNat % 2 ^ w) := by
  have hpw : 2 ^ w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hw'
  have hlow : v.toNat % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have hset : (v.setWidth w).toNat = v.toNat % 2 ^ w := by simp [BitVec.toNat_setWidth]
  have hmsb : (v.setWidth w).msb = decide (2 ^ (w - 1) ≤ v.toNat % 2 ^ w) := by
    rw [BitVec.msb_eq_decide, hset]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, hmsb, BitVec.toNat_setWidth, hset,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlow hpw)]
  by_cases hc : v.toNat % 2 ^ w < 2 ^ (w - 1)
  · rw [if_pos hc, decide_eq_false (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlow hpw)]
  · rw [if_neg hc, decide_eq_true (by omega)]
    simp only [↓reduceIte, BitVec.toNat_ofNat]
    have h2 : 2 ^ 256 - 2 ^ w + v.toNat % 2 ^ w < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt h2]
    omega

/-- EthLib's SIGNEXTEND is `EvmRules.Evm.signextend`. -/
theorem signextend_agree (b v : Word) : signextend b v = EvmRules.Evm.signextend b v := by
  unfold signextend
  by_cases hb : b.toNat > 31
  · rw [if_pos hb]
    have h0 : (b == 0) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h1 : (b == 1) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h2 : (b == 2) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h3 : (b == 3) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h4 : (b == 4) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h5 : (b == 5) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h6 : (b == 6) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h7 : (b == 7) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h8 : (b == 8) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h9 : (b == 9) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h10 : (b == 10) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h11 : (b == 11) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h12 : (b == 12) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h13 : (b == 13) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h14 : (b == 14) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h15 : (b == 15) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h16 : (b == 16) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h17 : (b == 17) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h18 : (b == 18) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h19 : (b == 19) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h20 : (b == 20) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h21 : (b == 21) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h22 : (b == 22) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h23 : (b == 23) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h24 : (b == 24) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h25 : (b == 25) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h26 : (b == 26) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h27 : (b == 27) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h28 : (b == 28) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h29 : (b == 29) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    have h30 : (b == 30) = false := by
      rw [beq_eq_false_iff_ne]; rintro rfl; simp at hb
    unfold EvmRules.Evm.signextend
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, Bool.cond_false]
  · rw [if_neg hb]
    have hb31 : b.toNat ≤ 31 := by omega
    obtain ⟨k, hk, rfl⟩ : ∃ k, k ≤ 31 ∧ b = BitVec.ofNat 256 k :=
      ⟨b.toNat, hb31, by simp⟩
    have hkn : (BitVec.ofNat 256 k).toNat = k := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [hkn, ← signExtend_low v (8 * (k + 1)) (by omega)]
    unfold EvmRules.Evm.signextend
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Exponentiation -/

/-- EthLib's square-and-multiply computes `b ^ e % m` (as `EthLib.Execution.Evm.powMod_eq`,
whose module the EthLib build this library links does not compile). -/
theorem powMod_eq' (b e m : Nat) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    rw [powMod]
    by_cases h0 : e = 0
    · subst h0
      simp
    · rw [dite_eq_right h0]
      have hrec := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) (b * b % m)
      have hhalf : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rw [hrec, hhalf]
      by_cases h1 : e % 2 = 1
      · rw [ite_eq_left h1, Nat.mod_mul_mod, ← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]
      · rw [ite_eq_right h1, show 2 * (e / 2) = e by omega]

/-- SolarTV's square-and-multiply on words is the power modulo `2^256`. -/
theorem power_toNat (a : Word) (n : Nat) :
    (SolarTV.Word.power a n).toNat = a.toNat ^ n % 2 ^ 256 := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [SolarTV.Word.power]
    by_cases h0 : n = 0
    · subst h0; simp
    · rw [dif_neg h0]
      have hh := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) (a * a)
      have hsq : (a * a).toNat ^ (n / 2) % 2 ^ 256 = a.toNat ^ (2 * (n / 2)) % 2 ^ 256 := by
        rw [BitVec.toNat_mul, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      by_cases h1 : n % 2 = 0
      · simp only [if_pos h1]
        rw [hh, hsq, show 2 * (n / 2) = n by omega]
      · simp only [if_neg h1]
        rw [BitVec.toNat_mul, hh, hsq, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_succ',
          show (2 * (n / 2)).succ = n by omega]

/-- EthLib's EXP is SolarTV's `Word.power` on the exponent's number. -/
theorem exp_agree (a b : Word) : exp a b = SolarTV.Word.power a b.toNat := by
  unfold exp
  rw [powMod_eq']
  apply BitVec.eq_of_toNat_eq
  rw [power_toNat, BitVec.toNat_ofNat, Nat.mod_mod]

/-- A word's exponent takes at most 32 bytes. -/
theorem exponentBytes_le (e : U256) : exponentBytes e ≤ 32 := by
  unfold exponentBytes bitLength
  split
  · omega
  · have := e.isLt
    have : e.toNat.log2 < 256 := (Nat.log2_lt (by omega)).2 this
    omega

/-- EXP costs at most 1610 at Fusaka. -/
theorem exp_cost_le (e : U256) :
    OPCODE_EXP_BASE + (gasSchedule .fusaka).OPCODE_EXP_PER_BYTE * exponentBytes e ≤ 1610 := by
  have h := exponentBytes_le e
  have hb : OPCODE_EXP_BASE = 10 := rfl
  have hp : (gasSchedule .fusaka).OPCODE_EXP_PER_BYTE = 50 := by decide
  rw [hb, hp]
  omega

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.sdiv_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sdiv_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.smod_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smod_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.sar_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sar_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.signextend_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signextend_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.exp_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_agree

/-- info: 'SolidCore.Refinement.Solar.AssembleSigned.exp_cost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exp_cost_le

end SolidCore.Refinement.Solar.AssembleSigned
