import Verify.Gas.FixedFuel.Measured

/-!
# A measure for a counter word that steps down by one to zero

`Measured` covers the layouts the backend gives a counted `for` loop: a counter word stepped by one
*up* to zero (`Measured.down`, entered as `0 - n`), a counter compared with its limit
(`Measured.up`) and a rotated loop. A loop that counts its limit itself down, as
`while (a > 0) { a--; ... }` does, reaches the final EVM IR in another layout: the header tests a
header word `w` (nonzero: iterate), every iteration returns with `w - 1` in its place, and the word
enters the header as the limit itself (a call argument, a storage word or a literal).

Its measure is the word's value, `dec k ws = (ws.getD k 0).toNat`: below `2 ^ 256` (`dec_lt`),
zero exactly when the word is zero (`dec_zero`, `dec_ne`, and for a header that tests `0 < w`,
`dec_pos`, `dec_not_pos`), lower after `w - 1` (or `w + (2 ^ 256 - 1)`) of a nonzero word
(`sub_one_lt`, `add_ones_lt`), and at most `K` on entry when the limit is (`dec_le`). These are
the lemmas a generated proof (solar's `tools/certify/loop_resources.py`, shape `dec`) passes to
`Measured.loops_of` with the guard `Measured.always`. Nothing here names a contract, a program or
a file.
-/

namespace Verify.Gas.FixedFuel.MeasuredDec

open SolarTV SolarTV.Machine

/-- Header word `k` steps by one down to zero: the iterations left are its value. -/
def dec (k : Nat) (ws : EVM.Stack) : Nat := (ws.getD k 0).toNat

/-- The measure is below `2 ^ 256`, as `Measured.loops_of` needs. -/
theorem dec_lt (k : Nat) (ws : EVM.Stack) : dec k ws < 2 ^ 256 := (ws.getD k 0).isLt

theorem toNat_eq_zero {w : EvmRules.Word} : w.toNat = 0 ↔ w = 0 := by
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  · rintro rfl
    rfl

/-- A counter word of measure zero is zero. -/
theorem dec_zero {w : EvmRules.Word} (h : w.toNat = 0) : w = 0 := toNat_eq_zero.1 h

/-- A counter word of nonzero measure is nonzero. -/
theorem dec_ne {w : EvmRules.Word} (h : w.toNat ≠ 0) : ¬w = 0 := fun e => h (toNat_eq_zero.2 e)

/-- A counter word of nonzero measure is above zero (a header that tests `0 < w`). -/
theorem dec_pos {w : EvmRules.Word} (h : w.toNat ≠ 0) : (0 : EvmRules.Word) < w := by
  rw [BitVec.lt_def]
  show 0 < w.toNat
  omega

/-- A counter word of measure zero is not above zero. -/
theorem dec_not_pos {w : EvmRules.Word} (h : w.toNat = 0) : ¬(0 : EvmRules.Word) < w := by
  rw [BitVec.lt_def]
  show ¬0 < w.toNat
  omega

/-- A word above zero is nonzero. -/
theorem ne_of_pos {w : EvmRules.Word} (h : (0 : EvmRules.Word) < w) : ¬w = 0 := by
  rintro rfl
  exact absurd h (BitVec.lt_irrefl _)

/-- One step down: `w - 1` of a nonzero word leaves fewer iterations. -/
theorem sub_one_lt {w : EvmRules.Word} (h : ¬w = 0) :
    (EvmRules.Evm.sub w 1).toNat < w.toNat := by
  have : w.toNat ≠ 0 := fun e => h (toNat_eq_zero.1 e)
  have := w.isLt
  unfold EvmRules.Evm.sub
  rw [BitVec.toNat_sub, show (1 : BitVec 256).toNat = 1 from rfl]
  omega

/-- One step down written as an addition of the all-ones word `c = 2 ^ 256 - 1`. -/
theorem add_ones_lt {w c : EvmRules.Word} (h : ¬w = 0) (hc : c.toNat = 2 ^ 256 - 1) :
    (EvmRules.Evm.add w c).toNat < w.toNat := by
  have : w.toNat ≠ 0 := fun e => h (toNat_eq_zero.1 e)
  have := w.isLt
  unfold EvmRules.Evm.add
  rw [BitVec.toNat_add, hc]
  omega

/-- `add_ones_lt` with the all-ones word first. -/
theorem add_ones_lt' {w c : EvmRules.Word} (h : ¬w = 0) (hc : c.toNat = 2 ^ 256 - 1) :
    (EvmRules.Evm.add c w).toNat < w.toNat := by
  rw [show EvmRules.Evm.add c w = EvmRules.Evm.add w c from BitVec.add_comm _ _]
  exact add_ones_lt h hc

/-- The entry: the measure of a header stack is at most `K` when its counter word's value is.
Stated over `dec`, so a use unifies with the goal's measure without unfolding the word. -/
theorem dec_le {k : Nat} {ws : EVM.Stack} {K : Nat} (h : (ws.getD k 0).toNat ≤ K) :
    dec k ws ≤ K :=
  h

/-! Every lemma rests on the standard axioms only. -/

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_lt

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_zero

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_ne

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_pos

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_not_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_not_pos

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.ne_of_pos' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ne_of_pos

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.sub_one_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sub_one_lt

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.add_ones_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_ones_lt

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.add_ones_lt'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_ones_lt'

/-- info: 'Verify.Gas.FixedFuel.MeasuredDec.dec_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms dec_le

end Verify.Gas.FixedFuel.MeasuredDec
