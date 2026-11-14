import SolidCore.Refinement.Wide.Tactic
import SolidCore.Refinement.Dirty.Source

/-!
# Rewrite rules for evaluating a call of a wide function in SolidCore

`Wide.Tactic`'s evaluator runs SolidCore's interpreter by unfolding it. A few of
its functions are better rewritten than unfolded, because unfolding them on a
free argument word gives a term no later step simplifies:

* the ABI decoder reads its argument words from `Dirty.argBytes args`, the call
  data after the selector; `readWord_argBytes'` reads a word back as the argument
  (rather than refolding 32 symbolic bytes), and `drop_selector` strips the
  selector;
* the encoder writes a returned word big-endian; `wordToBytesBE_eq` states it as
  EthLib's `natToBytes`, the form EthLib's return data takes;
* SolidCore's word operations (`Shared.addWord` and the rest) go through
  evmyul's `UInt256`, a `Fin`; `addWord_eq` and its siblings state them as
  operations on `BitVec 256`, the words of EthLib, and the comparisons as `if`s
  on the words' values, so that the source's results and branch conditions are
  terms `bv_decide` and `bv_omega` relate to the bytecode's.

`wide_symex [lemmas]` is `src_symex` with all of them.
-/

namespace SolidCore.Refinement.Wide

open EthLib.Base SolidCore.Solidity SolidCore.Solidity.Source

theorem drop_selector (sel : Nat) (args : List Nat) :
    ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop 4 = Dirty.argBytes args := by
  simp [natToBytes_length]

/-- The word at a word-aligned offset of the argument bytes is that argument. -/
theorem readWord_argBytes' (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) (off : Nat)
    (hmod : off % 32 = 0) (hlt : off / 32 < args.length) :
    ABI.readWord? (Dirty.argBytes args) off = some (args.getD (off / 32) 0) := by
  have := Dirty.readWord_argBytes args hargs (off / 32) hlt
  rw [show 32 * (off / 32) = off by omega] at this
  rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

theorem normByte_eq (v : Nat) : normByte v = v % 256 := by
  simp [normByte, Shared.Account.byte]

/-- SolidCore writes a word big-endian as EthLib does. -/
theorem wordToBytesBE_eq (n v : Nat) :
    ABI.wordToBytesBE n v = (natToBytes n v).map (·.toNat) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [ABI.wordToBytesBE, natToBytes_succ, ih, List.map_append]
    simp [normByte_eq]

/-! ## Word operations as bit-vector operations -/

namespace Words

open Shared

theorem toNat_ofNat_u256 (n : Nat) : (EvmYul.UInt256.ofNat n).toNat = n % 2 ^ 256 :=
  Fin.val_ofNat _ _
theorem toNat_add_u256 (x y : EvmYul.UInt256) : (x.add y).toNat = (x.toNat + y.toNat) % 2 ^ 256 :=
  Fin.val_add _ _
theorem toNat_sub_u256 (x y : EvmYul.UInt256) :
    (x.sub y).toNat = (2 ^ 256 - y.toNat + x.toNat) % 2 ^ 256 :=
  Fin.val_sub _ _
theorem toNat_mul_u256 (x y : EvmYul.UInt256) : (x.mul y).toNat = (x.toNat * y.toNat) % 2 ^ 256 :=
  Fin.val_mul _ _
theorem toNat_xor_u256 (x y : EvmYul.UInt256) :
    (x.xor y).toNat = (x.toNat ^^^ y.toNat) % 2 ^ 256 := by
  simp [EvmYul.UInt256.xor, EvmYul.UInt256.toNat, Fin.xor]; rfl
theorem toNat_land_u256 (x y : EvmYul.UInt256) :
    (x.land y).toNat = (x.toNat &&& y.toNat) % 2 ^ 256 := by
  simp [EvmYul.UInt256.land, EvmYul.UInt256.toNat, Fin.land]; rfl
theorem toNat_lor_u256 (x y : EvmYul.UInt256) :
    (x.lor y).toNat = (x.toNat ||| y.toNat) % 2 ^ 256 := by
  simp [EvmYul.UInt256.lor, EvmYul.UInt256.toNat, Fin.lor]; rfl

theorem size_eq : EvmYul.UInt256.size = 2 ^ 256 := rfl

end Words

open Shared Words in
theorem addWord_eq (a b : Nat) : addWord a b = (BitVec.ofNat 256 a + BitVec.ofNat 256 b).toNat := by
  simp only [addWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_add_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]

open Shared Words in
theorem subWord_eq (a b : Nat) : subWord a b = (BitVec.ofNat 256 a - BitVec.ofNat 256 b).toNat := by
  simp only [subWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_sub_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]

open Shared Words in
theorem mulWord_eq (a b : Nat) : mulWord a b = (BitVec.ofNat 256 a * BitVec.ofNat 256 b).toNat := by
  simp only [mulWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_mul_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]

open Shared Words in
theorem xorWord_eq (a b : Nat) : xorWord a b = (BitVec.ofNat 256 a ^^^ BitVec.ofNat 256 b).toNat := by
  simp only [xorWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_xor_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 256) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)))

open Shared Words in
theorem andWord_eq (a b : Nat) : andWord a b = (BitVec.ofNat 256 a &&& BitVec.ofNat 256 b).toNat := by
  simp only [andWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_land_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt (y := 2 ^ 256) _ (by decide)))

open Shared Words in
theorem orWord_eq (a b : Nat) : orWord a b = (BitVec.ofNat 256 a ||| BitVec.ofNat 256 b).toNat := by
  simp only [orWord, liftEvmBinary, ofEvmWord, toEvmWord, norm, Shared.wordModulus, toNat_lor_u256,
    toNat_ofNat_u256, EvmYul.UInt256.size, BitVec.toNat_or, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 256) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)))

open Shared Words in
theorem ltWord_eq (a b : Nat) : ltWord a b = if a % 2 ^ 256 < b % 2 ^ 256 then 1 else 0 := by
  have key : (EvmYul.UInt256.ofNat (norm a) < EvmYul.UInt256.ofNat (norm b)) ↔
      a % 2 ^ 256 < b % 2 ^ 256 := by
    show (EvmYul.UInt256.ofNat (norm a)).toNat < (EvmYul.UInt256.ofNat (norm b)).toNat ↔ _
    rw [toNat_ofNat_u256, toNat_ofNat_u256]
    simp [norm, Shared.wordModulus, EvmYul.UInt256.size]
  unfold ltWord liftEvmBinary ofEvmWord toEvmWord EvmYul.UInt256.lt EvmYul.UInt256.fromBool
    Bool.toUInt256
  by_cases h : a % 2 ^ 256 < b % 2 ^ 256
  · rw [if_pos (decide_eq_true (key.mpr h)), if_pos h]; rfl
  · rw [if_neg (by simpa using fun h' => h (key.mp h')), if_neg h]; rfl

open Shared in
theorem gtWord_eq (a b : Nat) : gtWord a b = if b % 2 ^ 256 < a % 2 ^ 256 then 1 else 0 := by
  rw [← ltWord_eq]; rfl

/-- The rewrite rules of a call of a wide function, for `src_symex`. -/
macro "wide_symex" " [" ts:term,* "]" : tactic =>
  `(tactic| src_symex [Dirty.readSelector_calldata, drop_selector, readWord_argBytes',
    wordToBytesBE_eq, Dirty.length_argBytes, addWord_eq, subWord_eq, mulWord_eq, xorWord_eq,
    andWord_eq, orWord_eq, ltWord_eq, gtWord_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq, $ts,*])

end SolidCore.Refinement.Wide
