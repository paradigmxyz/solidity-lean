import SolarTV.MIR.Ops
import SolarTV.MIR.Program

/-! Integer cleanup can remove a truncation after a lossless zero extension.
The concrete i160/i256 theorem also checks the native bit-vector width model.
The i1 examples pin the difference between truncation and boolean normalization,
and between sign and zero extension. The last two relate the lowered MIR semantics' casts
to these. -/

namespace SolarTV.MIR

theorem truncate_extended_address (value : BitVec 160) :
    cast .trunc 160 (cast .zext 256 value) = value := by
  simp [cast]

theorem truncate_even_word : cast .trunc 1 (2#256) = 0#1 := by decide

theorem extend_true_sign : cast .sext 256 (1#1) = -1#256 := by decide

theorem extend_true_zero : cast .zext 256 (1#1) = 1#256 := by decide

/-- The lowered semantics' truncation, `low`, is the typed one extended back to a word. -/
theorem lowBits_eq_trunc (bits : Nat) (le : bits ≤ 256) (w : BitVec 256) :
    Lowered.lowBits bits w = cast .zext 256 (cast .trunc bits w) := by
  have hp : 2 ^ bits ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) le
  apply BitVec.eq_of_toNat_eq
  simp [Lowered.lowBits, EvmRules.Evm.and, cast,
    Nat.mod_eq_of_lt (show 2 ^ bits - 1 < 2 ^ 256 by omega), Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hp)).symm

/-- The lowered semantics leaves a zero extension's word as it is (`word`), which is the typed
extension on every word whose bits above the source width are zero, as every MIR value's are. -/
theorem word_eq_zext (bits : Nat) (w : BitVec 256) (clean : w.toNat < 2 ^ bits) :
    w = cast .zext 256 (cast .trunc bits w) := by
  apply BitVec.eq_of_toNat_eq
  simp [cast, Nat.mod_eq_of_lt clean, Nat.mod_eq_of_lt w.isLt]

end SolarTV.MIR
