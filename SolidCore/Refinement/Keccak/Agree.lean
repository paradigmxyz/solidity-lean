import EthLib.Cryptography.Hash.Keccak
import EvmYul.SpongeHash.Keccak256

/-!
# EthLib's Keccak-256 and evmyul's agree on 64 bytes

SolidCore hashes with evmyul's pure Keccak-256 (`EvmYul.SpongeHash.Keccak256`: lanes as `Nat`s in a
list of 25, bitwise operations reduced mod 2^64) and EthLib with its own (`Hash.Keccak`: a record of
25 `UInt64` lanes). The two are separate definitions; this file proves them equal, structurally:

1. lanes: each of evmyul's lane operations (`bxor`, `band`, `bnot`, `rotl64`) on the `toNat` of
   `UInt64`s is the `toNat` of EthLib's (`toNat_xor'`, `toNat_and'`, `toNat_not'`, `toNat_rotl`);
2. the permutation: with EthLib's state read as evmyul's list (`toL`), each step mapping agrees
   (`theta_toL`; evmyul's `rhoPi` is EthLib's `pi ∘ rho`, `rhoPi_toL`; `chi_toL`; `iota_toL`), so
   every round does (`round_toL`), evmyul's round constants are EthLib's (`rc_get`) and the two
   Keccak-f[1600] agree on every state (`keccakF1600_toL`);
3. the sponge on a 64-byte message: both pad to the same one block of 136 bytes (`pad64`), absorb
   it into the same lanes (`absorb64`, each lane the little-endian number of its 8 bytes on both
   sides: `chainE`, `laneAt_toNat`), permute once, and squeeze the same first 32 bytes
   (`squeeze_toL`): `keccak256_64`.

The sponge is proved for 64-byte messages, the inputs a mapping's slot hashes (two words); the
permutation for every state. No sorry, native_decide or bv_decide; `decide +kernel` only on closed
tables.
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

theorem chainE (c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (h0 : c0 < 256) (h1 : c1 < 256) (h2 : c2 < 256)
    (h3 : c3 < 256) (h4 : c4 < 256) (h5 : c5 < 256) (h6 : c6 < 256) (h7 : c7 < 256) :
    E.bxor 0 (E.bxor c0 (E.bxor (c1 * 256) (E.bxor (c2 * 65536) (E.bxor (c3 * 16777216)
      (E.bxor (c4 * 4294967296) (E.bxor (c5 * 1099511627776)
        (E.bxor (c6 * 281474976710656) (c7 * 72057594037927936)))))))) =
      c0 + c1 * 256 + c2 * 65536 + c3 * 16777216 + c4 * 4294967296 + c5 * 1099511627776 +
        c6 * 281474976710656 + c7 * 72057594037927936 := by
  simp only [← bxor_assoc]
  rw [bxor_zero_left c0 (by omega),
    bxor_shift _ _ 256 8 rfl (by omega) (by omega),
    bxor_shift _ _ 65536 16 rfl (by omega) (by omega),
    bxor_shift _ _ 16777216 24 rfl (by omega) (by omega),
    bxor_shift _ _ 4294967296 32 rfl (by omega) (by omega),
    bxor_shift _ _ 1099511627776 40 rfl (by omega) (by omega),
    bxor_shift _ _ 281474976710656 48 rfl (by omega) (by omega),
    bxor_shift _ _ 72057594037927936 56 rfl (by omega) (by omega)]

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

theorem padding64 : (padding 136 64).data = #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128] := by decide

theorem pad64 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : UInt8) :
    pad 136 ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]⟩ = ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128]⟩ := by
  apply ByteArray.ext
  rw [pad, ByteArray.data_append, show ByteArray.size ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]⟩ = 64 from rfl, padding64]
  simp only [List.append_toArray, List.cons_append, List.nil_append]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem absorb64 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : UInt8) :
    E.absorbBlockFrom (List.replicate 25 0) 0 (E.padKeccak [b0.toNat, b1.toNat, b2.toNat, b3.toNat, b4.toNat, b5.toNat, b6.toNat, b7.toNat, b8.toNat, b9.toNat, b10.toNat, b11.toNat, b12.toNat, b13.toNat, b14.toNat, b15.toNat, b16.toNat, b17.toNat, b18.toNat, b19.toNat, b20.toNat, b21.toNat, b22.toNat, b23.toNat, b24.toNat, b25.toNat, b26.toNat, b27.toNat, b28.toNat, b29.toNat, b30.toNat, b31.toNat, b32.toNat, b33.toNat, b34.toNat, b35.toNat, b36.toNat, b37.toNat, b38.toNat, b39.toNat, b40.toNat, b41.toNat, b42.toNat, b43.toNat, b44.toNat, b45.toNat, b46.toNat, b47.toNat, b48.toNat, b49.toNat, b50.toNat, b51.toNat, b52.toNat, b53.toNat, b54.toNat, b55.toNat, b56.toNat, b57.toNat, b58.toNat, b59.toNat, b60.toNat, b61.toNat, b62.toNat, b63.toNat]) =
      toL (Internal.absorbBlock 136 State.zero (pad 136 ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]⟩) 0) := by
  rw [pad64]
  simp [E.padKeccak, E.rateBytes, E.absorbBlockFrom, E.absorbByte, E.byteShift, E.getD, E.setD, toL, Internal.absorbBlock,
      Internal.blockLane, laneAt_toNat, byteAt_mk, State.zero, chainE, toNat_lt256]
  all_goals decide

theorem chunksOf_single (bs : List Nat) (h : bs.length = 136) : E.chunksOf 136 bs = [bs] := by
  simp only [E.chunksOf, h]
  show E.chunksOfWithFuel (136 + 1) 136 bs = [bs]
  cases bs with
  | nil => simp at h
  | cons x xs =>
    rw [E.chunksOfWithFuel, List.take_of_length_le (Nat.le_of_eq h),
      List.drop_of_length_le (Nat.le_of_eq h)]
    all_goals first | rfl | simp

theorem keccak64_explicit (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : UInt8) :
    E.keccak256Bytes [b0.toNat, b1.toNat, b2.toNat, b3.toNat, b4.toNat, b5.toNat, b6.toNat, b7.toNat, b8.toNat, b9.toNat, b10.toNat, b11.toNat, b12.toNat, b13.toNat, b14.toNat, b15.toNat, b16.toNat, b17.toNat, b18.toNat, b19.toNat, b20.toNat, b21.toNat, b22.toNat, b23.toNat, b24.toNat, b25.toNat, b26.toNat, b27.toNat, b28.toNat, b29.toNat, b30.toNat, b31.toNat, b32.toNat, b33.toNat, b34.toNat, b35.toNat, b36.toNat, b37.toNat, b38.toNat, b39.toNat, b40.toNat, b41.toNat, b42.toNat, b43.toNat, b44.toNat, b45.toNat, b46.toNat, b47.toNat, b48.toNat, b49.toNat, b50.toNat, b51.toNat, b52.toNat, b53.toNat, b54.toNat, b55.toNat, b56.toNat, b57.toNat, b58.toNat, b59.toNat, b60.toNat, b61.toNat, b62.toNat, b63.toNat] =
      (keccak256 ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]⟩).toList.map UInt8.toNat := by
  rw [E.keccak256Bytes, show E.rateBytes = 136 from rfl, chunksOf_single _ (by simp [E.padKeccak, E.rateBytes])]
  simp only [E.absorbBlocks, E.absorbBlock]
  rw [absorb64, keccakF1600_toL, squeeze_toL, keccak256, spongeAbsorb]
  have hc : blockCount RATE (ByteArray.size ⟨#[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]⟩) = 1 := by
    simp [blockCount, RATE, ByteArray.size]
  rw [hc]
  rfl

theorem keccak256_64 (bs : List UInt8) (h : bs.length = 64) :
    E.keccak256Bytes (bs.map UInt8.toNat) = (keccak256 ⟨bs.toArray⟩).toList.map UInt8.toNat := by
  match bs, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: b16 :: b17 :: b18 :: b19 :: b20 :: b21 :: b22 :: b23 :: b24 :: b25 :: b26 :: b27 :: b28 :: b29 :: b30 :: b31 :: b32 :: b33 :: b34 :: b35 :: b36 :: b37 :: b38 :: b39 :: b40 :: b41 :: b42 :: b43 :: b44 :: b45 :: b46 :: b47 :: b48 :: b49 :: b50 :: b51 :: b52 :: b53 :: b54 :: b55 :: b56 :: b57 :: b58 :: b59 :: b60 :: b61 :: b62 :: b63 :: [], _ => exact keccak64_explicit b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63

#print axioms keccak256_64

/-! Concrete agreement, checked by the kernel, on messages the 64-byte theorem does not cover: the
empty message, one byte short of a block, a whole block (the padding a block of its own) and two
blocks. Evidence for the general statement, which is not proved here. -/

example : (keccak256 ⟨#[]⟩).toList.map UInt8.toNat = E.keccak256Bytes [] := by decide +kernel

example : (keccak256 ⟨(List.range 135).toArray.map UInt8.ofNat⟩).toList.map UInt8.toNat =
    E.keccak256Bytes (List.range 135) := by decide +kernel

example : (keccak256 ⟨(List.range 136).toArray.map UInt8.ofNat⟩).toList.map UInt8.toNat =
    E.keccak256Bytes (List.range 136) := by decide +kernel

example : (keccak256 ⟨(List.range 200).toArray.map UInt8.ofNat⟩).toList.map UInt8.toNat =
    E.keccak256Bytes (List.range 200) := by decide +kernel

end SolidCore.Refinement.Keccak
