import EthLib.Cryptography.Hash.Keccak
import EvmYul.SpongeHash.Keccak256

/-!
# EthLib's Keccak-256 and evmyul's agree on every message

SolidCore hashes with evmyul's pure Keccak-256 (`EvmYul.SpongeHash.Keccak256`: lanes as `Nat`s in a
list of 25, bitwise operations reduced mod 2^64) and EthLib with its own (`Hash.Keccak`: a record of
25 `UInt64` lanes). The two are separate definitions; this file proves them equal, structurally:

1. lanes: each of evmyul's lane operations (`bxor`, `band`, `bnot`, `rotl64`) on the `toNat` of
   `UInt64`s is the `toNat` of EthLib's (`toNat_xor'`, `toNat_and'`, `toNat_not'`, `toNat_rotl`);
2. the permutation: with EthLib's state read as evmyul's list (`toL`), each step mapping agrees
   (`theta_toL`; evmyul's `rhoPi` is EthLib's `pi ∘ rho`, `rhoPi_toL`; `chi_toL`; `iota_toL`), so
   every round does (`round_toL`), evmyul's round constants are EthLib's (`rc_get`) and the two
   Keccak-f[1600] agree on every state (`keccakF1600_toL`);
3. the sponge on every message: both pad the same way (`pad_toList`: pad10*1, one byte `0x81`
   when one byte of the block is left), cut the padded message into the same blocks of 136 bytes,
   absorb each into the same lanes from any state (`absorbBlock_toL`: byte by byte on evmyul's
   side, `absorbLane`; each lane the little-endian number of its 8 bytes on EthLib's,
   `laneAt_toNat`), permute after each (`absorbBlocks_toL`), and squeeze the same first 32 bytes
   (`squeeze_toL`): `keccak256_eq`, for every input length. `keccak256_64` is its 64-byte case.

The sponge is proved for every message and the permutation for every state. No sorry,
native_decide or bv_decide; `decide +kernel` only on closed tables.
-/


namespace SolidCore.Refinement.Keccak

open EthLib.Cryptography.Hash.Keccak
namespace E
export EvmYul.SpongeHash.Keccak256 (absorbBlockFrom absorbByte byteShift squeezeBytes laneBytesLE laneByte padKeccak chunksOf chunksOfWithFuel absorbBlocks absorbBlock keccak256Bytes rateBytes bxor band bnot rotl64 u64 word64 mask64 getD setD lane laneIndex
  xorList columnXor theta rhoPi rhoPiSet chi iota round permute keccakF1600 roundConstants rhoOffset)
end E

/-- EthLib's state as evmyul's list of 25 lanes. -/
def toL (A : State) : List Nat :=
  [A.a0.toNat, A.a1.toNat, A.a2.toNat, A.a3.toNat, A.a4.toNat, A.a5.toNat, A.a6.toNat, A.a7.toNat,
   A.a8.toNat, A.a9.toNat, A.a10.toNat, A.a11.toNat, A.a12.toNat, A.a13.toNat, A.a14.toNat,
   A.a15.toNat, A.a16.toNat, A.a17.toNat, A.a18.toNat, A.a19.toNat, A.a20.toNat, A.a21.toNat,
   A.a22.toNat, A.a23.toNat, A.a24.toNat]

theorem u64_toNat (a : UInt64) : E.u64 a.toNat = a.toNat :=
  Nat.mod_eq_of_lt a.toNat_lt

theorem toNat_xor' (a b : UInt64) : (a ^^^ b).toNat = E.bxor a.toNat b.toNat := by
  simp only [E.bxor, u64_toNat, UInt64.toNat_xor]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.toNat_lt b.toNat_lt)).symm

theorem toNat_and' (a b : UInt64) : (a &&& b).toNat = E.band a.toNat b.toNat := by
  simp only [E.band, u64_toNat, UInt64.toNat_and]
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ b.toNat_lt)).symm

theorem toNat_not' (a : UInt64) : (~~~a).toNat = E.bnot a.toNat := by
  simp only [E.bnot, u64_toNat, UInt64.toNat_not]; rfl

theorem toNat_rotl (a r : UInt64) (hr : r.toNat < 64) : (rotl a r).toNat = E.rotl64 a.toNat r.toNat := by
  have ha := a.toNat_lt
  simp only [rotl, E.rotl64, u64_toNat, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
  by_cases h0 : r.toNat = 0
  · have : (64 - r).toNat = 64 := by
      rw [UInt64.toNat_sub_of_le] <;> simp_all [UInt64.le_iff_toNat_le]
    simp [h0, this, Nat.mod_eq_of_lt ha]
  · have h64 : (64 - r).toNat = 64 - r.toNat := by
      rw [UInt64.toNat_sub_of_le]; · rfl
      rw [UInt64.le_iff_toNat_le]; simp; omega
    have hn : r.toNat % 64 = r.toNat := Nat.mod_eq_of_lt hr
    have hm : (64 - r.toNat) % 64 = 64 - r.toNat := Nat.mod_eq_of_lt (by omega)
    have hb : (r.toNat == 0) = false := by simp [h0]
    simp only [h64, hn, hm, hb, Bool.false_eq_true, ite_false]
    generalize r.toNat = n at *
    generalize a.toNat = x at *
    have hw : (2:Nat) ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
    have hsl : x <<< n % 2 ^ 64 = (x % 2 ^ (64 - n)) <<< n := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, hw, Nat.mul_mod_mul_right]
    have hlt : x >>> (64 - n) < 2 ^ n := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul ((Nat.two_pow_pos _)), ← Nat.pow_add]
      calc x < 2 ^ 64 := ha
        _ = _ := by congr 1; omega
    rw [hsl, ← Nat.shiftLeft_add_eq_or_of_lt hlt, ← hsl, Nat.shiftLeft_eq, ← Nat.shiftRight_eq_div_pow]
    show _ = (x * 2 ^ n % 2 ^ 64 + x >>> (64 - n)) % 18446744073709551616
    symm; apply Nat.mod_eq_of_lt
    have h1 : x * 2 ^ n % 2 ^ 64 = (x % 2 ^ (64 - n)) * 2 ^ n := by rw [hw, Nat.mul_mod_mul_right]
    have h2 : x % 2 ^ (64 - n) + 1 ≤ 2 ^ (64 - n) := Nat.mod_lt _ ((Nat.two_pow_pos _))
    have h3 : (x % 2 ^ (64 - n) + 1) * 2 ^ n ≤ 2 ^ 64 := by rw [hw]; exact Nat.mul_le_mul_right _ h2
    rw [h1]; show _ < 2 ^ 64
    have : (x % 2 ^ (64 - n) + 1) * 2 ^ n = x % 2 ^ (64 - n) * 2 ^ n + 2 ^ n := Nat.succ_mul _ _
    omega

theorem nat_xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

theorem bxor_assoc (a b c : Nat) : E.bxor (E.bxor a b) c = E.bxor a (E.bxor b c) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [E.bxor, E.u64, E.word64, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, nat_xor_eq,
    Nat.testBit_mod_two_pow, Nat.testBit_xor]
  cases decide (i < 64) <;> simp

theorem bxor_zero (a : UInt64) : E.bxor a.toNat 0 = a.toNat := by
  rw [← UInt64.toNat_zero, ← toNat_xor', UInt64.xor_zero]

theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
theorem range25 : List.range 25 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24] := rfl

attribute [local simp] toNat_xor' toNat_and' toNat_not' bxor_assoc bxor_zero
attribute [-simp] UInt64.toNat_xor UInt64.toNat_and UInt64.toNat_not

theorem theta_toL (A : State) : E.theta (toL A) = toL (theta A) := by
  simp [E.theta, theta, toL, E.columnXor, E.xorList, E.lane, E.laneIndex, E.getD, range5, range25,
    toNat_rotl]

theorem rhoPi_toL (A : State) : E.rhoPi (toL A) = toL (pi (rho A)) := by
  simp [E.rhoPi, E.rhoPiSet, pi, rho, toL, E.lane, E.laneIndex, E.getD, E.setD, range5, toNat_rotl,
    E.rhoOffset]

theorem chi_toL (A : State) : E.chi (toL A) = toL (chi A) := by
  simp [E.chi, chi, toL, E.lane, E.laneIndex, E.getD, range25]

theorem iota_toL (ir : Fin ROUNDS) (A : State) : E.iota (toL A) (RC[ir]).toNat = toL (iota ir A) := by
  simp [E.iota, iota, toL, E.getD, E.setD]

theorem round_toL (ir : Fin ROUNDS) (A : State) :
    E.round (toL A) (RC[ir]).toNat = toL (round ir A) := by
  rw [E.round, round, theta_toL, rhoPi_toL, chi_toL, iota_toL]

theorem rc_get : ∀ i (h : i < 24), E.roundConstants[i]? = some (RC[i]'h).toNat := by
  decide +kernel

theorem permute_drop : ∀ n i, i + n = 24 → ∀ A,
    E.permute (toL A) (E.roundConstants.drop i) = toL (keccakF.roundsFrom i A)
  | 0, i, h, A => by
    obtain rfl : i = 24 := by omega
    rw [keccakF.roundsFrom]; simp [ROUNDS]; rfl
  | n + 1, i, h, A => by
    have hi : i < 24 := by omega
    have hl : i < E.roundConstants.length := by show i < 24; omega
    rw [List.drop_eq_getElem_cons hl]
    have hv : E.roundConstants[i] = (RC[i]'hi).toNat := by
      have := rc_get i hi; rw [List.getElem?_eq_getElem hl] at this; exact Option.some.inj this
    rw [hv, E.permute, show E.round (toL A) (RC[i]'hi).toNat = toL (round ⟨i, hi⟩ A) from round_toL ⟨i, hi⟩ A,
      permute_drop n (i + 1) (by omega)]
    conv => rhs; rw [keccakF.roundsFrom]
    simp [ROUNDS, hi]

theorem keccakF1600_toL (A : State) : E.keccakF1600 (toL A) = toL (keccakF A) :=
  permute_drop 24 0 rfl A

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem squeeze_toL (A : State) :
    E.squeezeBytes (toL A) = (Internal.squeeze A).toList.map UInt8.toNat := by
  simp [E.squeezeBytes, E.laneBytesLE, E.laneByte, E.getD, toL, Internal.squeeze, Internal.bytesOfLane,
    range25, range8, Nat.shiftRight_eq_div_pow]

theorem toNat_lt256 (b : UInt8) : b.toNat < 256 := b.toNat_lt

theorem byteAt_mk (l : List UInt8) (i : Nat) : EthLib.Base.byteAt ⟨l.toArray⟩ i = l.getD i 0 := by
  simp only [EthLib.Base.byteAt, ByteArray.size, List.size_toArray, List.getD_eq_getElem?_getD]
  split
  · rename_i h; simp [h, ByteArray.getElem_eq_getElem_data]
  · rename_i h; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem xor_shift (x y m : Nat) (hx : x < 2 ^ m) : x ^^^ y * 2 ^ m = x + y * 2 ^ m := by
  rw [Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hx]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : m ≤ i
  · have : x.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
    simp [this, hi]
  · simp [hi]

theorem or_shift (x y m : Nat) (hx : x < 2 ^ m) : x ||| y <<< m = x + y * 2 ^ m := by
  rw [Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hx, Nat.or_comm]

theorem bxor_shift (x y N m : Nat) (hN : N = 2 ^ m) (hx : x < N) (h : x + y * N < 2 ^ 64) :
    E.bxor x (y * N) = x + y * N := by
  subst hN
  have hy : y * 2 ^ m < 2 ^ 64 := by omega
  have hx64 : x < 2 ^ 64 := by omega
  simp only [E.bxor, E.u64, E.word64, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl,
    Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hy, nat_xor_eq, xor_shift x y m hx, Nat.mod_eq_of_lt h]

theorem bxor_zero_left (x : Nat) (h : x < 2 ^ 64) : E.bxor 0 x = x := by
  simp only [E.bxor, E.u64, E.word64, show (18446744073709551616 : Nat) = 2 ^ 64 from rfl, Nat.zero_mod,
    Nat.mod_eq_of_lt h, nat_xor_eq, Nat.zero_xor]

theorem laneAt_toNat (bytes : ByteArray) (s : Nat) :
    (Internal.laneAt bytes s).toNat =
      (EthLib.Base.byteAt bytes s).toNat + (EthLib.Base.byteAt bytes (s + 1)).toNat * 256 +
      (EthLib.Base.byteAt bytes (s + 2)).toNat * 65536 +
      (EthLib.Base.byteAt bytes (s + 3)).toNat * 16777216 +
      (EthLib.Base.byteAt bytes (s + 4)).toNat * 4294967296 +
      (EthLib.Base.byteAt bytes (s + 5)).toNat * 1099511627776 +
      (EthLib.Base.byteAt bytes (s + 6)).toNat * 281474976710656 +
      (EthLib.Base.byteAt bytes (s + 7)).toNat * 72057594037927936 := by
  have h0 := toNat_lt256 (EthLib.Base.byteAt bytes s)
  have h1 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 1))
  have h2 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 2))
  have h3 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 3))
  have h4 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 4))
  have h5 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 5))
  have h6 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 6))
  have h7 := toNat_lt256 (EthLib.Base.byteAt bytes (s + 7))
  simp only [Internal.laneAt, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  generalize (EthLib.Base.byteAt bytes s).toNat = c0 at *
  generalize (EthLib.Base.byteAt bytes (s + 1)).toNat = c1 at *
  generalize (EthLib.Base.byteAt bytes (s + 2)).toNat = c2 at *
  generalize (EthLib.Base.byteAt bytes (s + 3)).toNat = c3 at *
  generalize (EthLib.Base.byteAt bytes (s + 4)).toNat = c4 at *
  generalize (EthLib.Base.byteAt bytes (s + 5)).toNat = c5 at *
  generalize (EthLib.Base.byteAt bytes (s + 6)).toNat = c6 at *
  generalize (EthLib.Base.byteAt bytes (s + 7)).toNat = c7 at *
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show c1 <<< 8 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c2 <<< 16 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c3 <<< 24 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c4 <<< 32 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c5 <<< 40 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c6 <<< 48 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show c7 <<< 56 < 2 ^ 64 by rw [Nat.shiftLeft_eq]; omega)]
  rw [or_shift c0 c1 8 (by omega), or_shift _ c2 16 (by omega),
    or_shift _ c3 24 (by omega),
    or_shift _ c4 32 (by omega),
    or_shift _ c5 40 (by omega),
    or_shift _ c6 48 (by omega),
    or_shift _ c7 56 (by omega)]

/-! ## evmyul's list operations -/

theorem length_setD : ∀ (xs : List Nat) (i v : Nat), (E.setD xs i v).length = xs.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, v => by simp only [E.setD, List.length_cons, length_setD xs i v]

theorem getD_setD_self : ∀ (xs : List Nat) (i v : Nat), i < xs.length → E.getD (E.setD xs i v) i = v
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, v, h => getD_setD_self xs i v (by simp at h; omega)

theorem setD_setD : ∀ (xs : List Nat) (i v w : Nat), E.setD (E.setD xs i v) i w = E.setD xs i w
  | [], _, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, i + 1, v, w => by simp only [E.setD, setD_setD xs i v w]

theorem absorbBlockFrom_append : ∀ (xs ys : List Nat) (st : List Nat) (i : Nat),
    E.absorbBlockFrom st i (xs ++ ys) = E.absorbBlockFrom (E.absorbBlockFrom st i xs) (i + xs.length) ys
  | [], _, _, _ => rfl
  | x :: xs, ys, st, i => by
    simp only [List.cons_append, E.absorbBlockFrom, List.length_cons]
    rw [absorbBlockFrom_append xs ys, Nat.add_assoc, Nat.add_comm 1]

/-! ## A lane: 8 bytes absorbed one by one are the lane of their little-endian number -/

theorem chain8 (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 < 256) (h1 : c1 < 256) (h2 : c2 < 256)
    (h3 : c3 < 256) (h4 : c4 < 256) (h5 : c5 < 256) (h6 : c6 < 256) (h7 : c7 < 256) :
    E.bxor c0 (E.bxor (c1 * 256) (E.bxor (c2 * 65536) (E.bxor (c3 * 16777216)
      (E.bxor (c4 * 4294967296) (E.bxor (c5 * 1099511627776)
        (E.bxor (c6 * 281474976710656) (c7 * 72057594037927936))))))) =
      c0 + c1 * 256 + c2 * 65536 + c3 * 16777216 + c4 * 4294967296 + c5 * 1099511627776 +
        c6 * 281474976710656 + c7 * 72057594037927936 := by
  simp only [← bxor_assoc]
  rw [bxor_shift _ _ 256 8 rfl (by omega) (by omega),
    bxor_shift _ _ 65536 16 rfl (by omega) (by omega),
    bxor_shift _ _ 16777216 24 rfl (by omega) (by omega),
    bxor_shift _ _ 4294967296 32 rfl (by omega) (by omega),
    bxor_shift _ _ 1099511627776 40 rfl (by omega) (by omega),
    bxor_shift _ _ 281474976710656 48 rfl (by omega) (by omega),
    bxor_shift _ _ 72057594037927936 56 rfl (by omega) (by omega)]

theorem absorbByte_lane (st : List Nat) (l k c : Nat) (hk : k < 8) (hc : c < 256) :
    E.absorbByte st (8 * l + k) c = E.setD st l (E.bxor (E.getD st l) (c * 2 ^ (8 * k))) := by
  have h1 : (8 * l + k) / 8 = l := by omega
  have h2 : (8 * l + k) % 8 = k := by omega
  simp only [E.absorbByte, E.byteShift, h1, h2, Nat.mod_eq_of_lt hc]

theorem absorbByte_set (st : List Nat) (l k c v : Nat) (hl : l < st.length) (hk : k < 8) (hc : c < 256) :
    E.absorbByte (E.setD st l v) (8 * l + k) c = E.setD st l (E.bxor v (c * 2 ^ (8 * k))) := by
  rw [absorbByte_lane _ l k c hk hc, getD_setD_self _ _ _ hl, setD_setD]

theorem absorbLane (st : List Nat) (l : Nat) (hl : l < st.length) (c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (h0 : c0 < 256) (h1 : c1 < 256) (h2 : c2 < 256) (h3 : c3 < 256) (h4 : c4 < 256) (h5 : c5 < 256)
    (h6 : c6 < 256) (h7 : c7 < 256) :
    E.absorbBlockFrom st (8 * l) [c0, c1, c2, c3, c4, c5, c6, c7] =
      E.setD st l (E.bxor (E.getD st l) (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216 +
        c4 * 4294967296 + c5 * 1099511627776 + c6 * 281474976710656 + c7 * 72057594037927936)) := by
  have e0 := absorbByte_lane st l 0 c0 (by omega) h0
  rw [Nat.add_zero] at e0
  simp only [E.absorbBlockFrom, Nat.add_assoc, Nat.reduceAdd]
  rw [e0, absorbByte_set _ l 1 _ _ hl (by omega) h1, absorbByte_set _ l 2 _ _ hl (by omega) h2,
    absorbByte_set _ l 3 _ _ hl (by omega) h3, absorbByte_set _ l 4 _ _ hl (by omega) h4,
    absorbByte_set _ l 5 _ _ hl (by omega) h5, absorbByte_set _ l 6 _ _ hl (by omega) h6,
    absorbByte_set _ l 7 _ _ hl (by omega) h7]
  congr 1
  simp only [bxor_assoc, Nat.reduceMul, Nat.reducePow, Nat.mul_one]
  rw [chain8 _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7]
  simp only [Nat.add_assoc]

/-! ## A block: 17 lanes -/

/-- The little-endian number of the 8 bytes `f j` to `f (j + 7)`. -/
def laneVal (f : Nat → Nat) (j : Nat) : Nat :=
  f j + f (j + 1) * 256 + f (j + 2) * 65536 + f (j + 3) * 16777216 + f (j + 4) * 4294967296 +
    f (j + 5) * 1099511627776 + f (j + 6) * 281474976710656 + f (j + 7) * 72057594037927936

/-- Lanes `l` to `l + m - 1` of the state, each XORed with the lane its 8 bytes of `f` spell. -/
def lanesFrom : List Nat → (Nat → Nat) → Nat → Nat → List Nat
  | st, _, _, 0 => st
  | st, f, l, m + 1 => lanesFrom (E.setD st l (E.bxor (E.getD st l) (laneVal f (8 * l)))) f (l + 1) m

theorem absorbLanes (f : Nat → Nat) (hf : ∀ j, f j < 256) : ∀ (m : Nat) (st : List Nat) (l : Nat),
    l + m ≤ st.length →
    E.absorbBlockFrom st (8 * l) ((List.range' (8 * l) (8 * m)).map f) = lanesFrom st f l m
  | 0, st, l, _ => by simp [lanesFrom, E.absorbBlockFrom]
  | m + 1, st, l, h => by
    rw [show 8 * (m + 1) = 8 + 8 * m by omega, ← List.range'_append_1, List.map_append,
      absorbBlockFrom_append]
    have hr : (List.range' (8 * l) 8).map f = [f (8 * l), f (8 * l + 1), f (8 * l + 2), f (8 * l + 3),
        f (8 * l + 4), f (8 * l + 5), f (8 * l + 6), f (8 * l + 7)] := by
      rfl
    rw [hr, absorbLane st l (by omega) _ _ _ _ _ _ _ _ (hf _) (hf _) (hf _) (hf _) (hf _) (hf _) (hf _) (hf _)]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    rw [show 8 * l + 8 = 8 * (l + 1) by omega,
      absorbLanes f hf m _ (l + 1) (by rw [length_setD]; omega)]
    rfl

theorem size_eq (Q : ByteArray) : Q.size = Q.data.toList.length := rfl

theorem byteAt_eq (Q : ByteArray) (i : Nat) : EthLib.Base.byteAt Q i = Q.data.toList.getD i 0 := by
  have := byteAt_mk Q.data.toList i
  simpa using this

theorem block_eq (Q : ByteArray) (s : Nat) (h : s + 136 ≤ Q.size) :
    ((Q.data.toList.map UInt8.toNat).drop s).take 136 =
      (List.range' 0 136).map (fun j => (EthLib.Base.byteAt Q (s + j)).toNat) := by
  rw [size_eq] at h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range']; omega
  · intro i h1 h2
    have hi : i < 136 := by simpa only [List.length_map, List.length_range'] using h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range', byteAt_eq]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp

theorem lanes_toL (S : State) (Q : ByteArray) (s : Nat) :
    lanesFrom (toL S) (fun j => (EthLib.Base.byteAt Q (s + j)).toNat) 0 17 =
      toL (Internal.absorbBlock 136 S Q s) := by
  simp [lanesFrom, toL, E.setD, E.getD, laneVal, Internal.absorbBlock, Internal.blockLane,
    laneAt_toNat, Nat.add_assoc]

/-- A block of 136 bytes from `s` on, absorbed and permuted from any state, is EthLib's. -/
theorem absorbBlock_toL (S : State) (Q : ByteArray) (s : Nat) (h : s + 136 ≤ Q.size) :
    E.absorbBlock (toL S) (((Q.data.toList.map UInt8.toNat).drop s).take 136) =
      toL (keccakF (Internal.absorbBlock 136 S Q s)) := by
  rw [E.absorbBlock, block_eq Q s h,
    (absorbLanes (fun j => (EthLib.Base.byteAt Q (s + j)).toNat) (fun j => toNat_lt256 _) 17 (toL S) 0
      (by simp [toL]) : E.absorbBlockFrom (toL S) 0 ((List.range' 0 136).map _) = _),
    lanes_toL, keccakF1600_toL]

/-! ## Every block -/

theorem chunks_nil : ∀ fuel, E.chunksOfWithFuel fuel 136 [] = []
  | 0 => rfl
  | _ + 1 => rfl

/-- The `n` blocks from `s` on, cut and absorbed by evmyul, are the `n` blocks EthLib absorbs in
place. -/
theorem absorbBlocks_toL (Q : ByteArray) : ∀ (n fuel s : Nat) (S : State), s + 136 * n = Q.size →
    n ≤ fuel →
    E.absorbBlocks (toL S) (E.chunksOfWithFuel fuel 136 ((Q.data.toList.map UInt8.toNat).drop s)) =
      toL (Internal.absorbBlocks keccakF 136 Q n s S)
  | 0, fuel, s, S, h, _ => by
    have : (Q.data.toList.map UInt8.toNat).drop s = [] :=
      List.drop_eq_nil_of_le (by rw [size_eq] at h; rw [List.length_map]; omega)
    rw [this, chunks_nil]; rfl
  | n + 1, 0, _, _, _, hf => absurd hf (by omega)
  | n + 1, fuel + 1, s, S, h, hf => by
    have hne : (Q.data.toList.map UInt8.toNat).drop s ≠ [] := by
      intro he
      have := congrArg List.length he
      rw [List.length_drop, List.length_map, List.length_nil] at this
      rw [size_eq] at h; omega
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    rw [hx, E.chunksOfWithFuel, ← hx, E.absorbBlocks, absorbBlock_toL S Q s (by omega), List.drop_drop,
      Internal.absorbBlocks]
    · exact absorbBlocks_toL Q n fuel (s + 136) _ (by omega) (by omega)
    · exact List.cons_ne_nil x xs

/-! ## Padding -/

theorem modify_last {α} (f : α → α) (a x : α) : ∀ j,
    (List.replicate j a ++ [x]).modify j f = List.replicate j a ++ [f x]
  | 0 => rfl
  | j + 1 => by
    simp only [List.replicate_succ, List.cons_append, List.modify_succ_cons, modify_last f a x j]

/-- EthLib's `k` bytes of padding are evmyul's. -/
theorem padBytes (k : Nat) (hk : 1 ≤ k) :
    (((Array.replicate k (0 : UInt8)).modify 0 (· ||| 0x01)).modify (k - 1) (· ||| 0x80)).toList.map
      UInt8.toNat = if k == 1 then [0x81] else [0x01] ++ List.replicate (k - 2) 0 ++ [0x80] := by
  match k, hk with
  | 1, _ => decide
  | j + 2, _ =>
    simp only [Array.toList_modify, Array.toList_replicate]
    rw [show List.replicate (j + 2) (0 : UInt8) = 0 :: (List.replicate j 0 ++ [0]) by
      rw [List.replicate_succ, List.replicate_succ']]
    simp only [List.modify_zero_cons, show j + 2 - 1 = j + 1 by omega, List.modify_succ_cons,
      modify_last, List.map_cons, List.map_append, List.map_replicate]
    simp

/-- The padded message is evmyul's (`padKeccak`). -/
theorem pad_toList (bs : List UInt8) :
    (pad 136 ⟨bs.toArray⟩).data.toList.map UInt8.toNat = E.padKeccak (bs.map UInt8.toNat) := by
  have hb : ByteArray.size ⟨bs.toArray⟩ = bs.length := by simp [ByteArray.size]
  rw [pad, ByteArray.data_append, Array.toList_append, List.map_append, hb, padding]
  dsimp only
  rw [padBytes _ (by omega)]
  simp only [E.padKeccak, E.rateBytes, List.length_map, List.append_assoc]
  split <;> simp_all

theorem pad_size (bs : List UInt8) :
    (pad 136 ⟨bs.toArray⟩).size = 136 * (bs.length / 136 + 1) := by
  simp only [pad, padding, ByteArray.size]
  simp
  omega

/-! ## Keccak-256 on every message -/

/-- **EthLib's Keccak-256 and evmyul's agree on every message**: the same padding, the same blocks
absorbed into the same lanes, the same Keccak-f[1600] after each, the same squeeze. -/
theorem keccak256_eq (bs : List UInt8) :
    E.keccak256Bytes (bs.map UInt8.toNat) = (keccak256 ⟨bs.toArray⟩).toList.map UInt8.toNat := by
  have hpad := pad_toList bs
  have hsize := pad_size bs
  have key := absorbBlocks_toL (pad 136 ⟨bs.toArray⟩) (bs.length / 136 + 1)
    (((pad 136 ⟨bs.toArray⟩).data.toList.map UInt8.toNat).length + 1) 0 State.zero
    (by omega) (by rw [size_eq] at hsize; rw [List.length_map]; omega)
  rw [List.drop_zero] at key
  rw [E.keccak256Bytes, ← hpad, show E.rateBytes = 136 from rfl,
    show ∀ P, E.chunksOf 136 P = E.chunksOfWithFuel (P.length + 1) 136 P from fun _ => rfl,
    show List.replicate 25 0 = toL State.zero from rfl, key, squeeze_toL]
  rfl

#print axioms keccak256_eq

/-- EthLib's Keccak-256 and evmyul's agree on 64-byte messages, the inputs a mapping's slot hashes
(two words): `keccak256_eq` at that length. -/
theorem keccak256_64 (bs : List UInt8) (h : bs.length = 64) :
    E.keccak256Bytes (bs.map UInt8.toNat) = (keccak256 ⟨bs.toArray⟩).toList.map UInt8.toNat := by
  have _ := h
  exact keccak256_eq bs

#print axioms keccak256_64

end SolidCore.Refinement.Keccak
