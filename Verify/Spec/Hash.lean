import Verify.Spec.Semantics
import SolidCore.Refinement.Generic.Source
import Verify.Spec.TrustedBase.Hypotheses

/-!
# SolidCore's storage hash is the spec's

SolidCore hashes a mapping slot as `solHash k s` (its interpreter's `keccakWord` of the 64 bytes
of `k` and `s`, through `wordToBytesBE` and `bytesToWordBE`); the spec semantics reads the
same slot as `SolidCore.Spec.keccakWord (wordBytes k ++ wordBytes s)`. Both use EvmYul's
Keccak-256 sponge, whose output is 32 bytes each below 256, so the two are equal
(`solHash_eq`): a spec over mappings reads the slots SolidCore writes, with no hypothesis.
-/

namespace SolidCore.Spec

open EvmYul.SpongeHash.Keccak256 in
theorem squeezeBytes_lt (st : List Nat) : ∀ b ∈ squeezeBytes st, b < 256 := by
  intro b hb
  unfold squeezeBytes at hb
  have := List.mem_of_mem_take hb
  simp only [List.mem_flatMap, laneBytesLE, List.mem_map, laneByte] at this
  obtain ⟨_, _, _, _, rfl⟩ := this
  exact Nat.mod_lt _ (by decide)

open EvmYul.SpongeHash.Keccak256 in
theorem squeezeBytes_length (st : List Nat) : (squeezeBytes st).length = 32 := by
  simp [squeezeBytes, laneBytesLE, List.length_flatMap]

theorem foldl_bytes_lt : ∀ (l : List Nat) (acc : Nat), (∀ b ∈ l, b < 256) →
    l.foldl (fun a b => a * 256 + b) acc < (acc + 1) * 256 ^ l.length
  | [], acc, _ => by simp
  | b :: l, acc, h => by
    have hb := h b (List.mem_cons_self ..)
    have ih := foldl_bytes_lt l (acc * 256 + b) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    calc _ < (acc * 256 + b + 1) * 256 ^ l.length := ih
      _ ≤ (acc + 1) * 256 * 256 ^ l.length := Nat.mul_le_mul_right _ (by omega)
      _ = (acc + 1) * (256 ^ l.length * 256) := by rw [Nat.mul_assoc, Nat.mul_comm 256]

theorem foldl_norm : ∀ (l : List Nat) (acc : Nat), (∀ b ∈ l, b < 256) →
    l.foldl (fun a b => a * 256 + SolidCore.Solidity.Source.normByte b) acc =
      l.foldl (fun a b => a * 256 + b) acc
  | [], _, _ => rfl
  | b :: l, acc, h => by
    have hb := h b (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [show SolidCore.Solidity.Source.normByte b = b from Nat.mod_eq_of_lt hb]
    exact foldl_norm l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem keccakWord_eq (l : List Nat) :
    SolidCore.Solidity.Source.keccakWord l = keccakWord l := by
  unfold SolidCore.Solidity.Source.keccakWord keccakWord SolidCore.Solidity.Source.bytesToWordBE bytesWord
  have hk : SolidCore.Solidity.Source.Keccak.keccak256Bytes l =
      EvmYul.SpongeHash.Keccak256.keccak256Bytes l := rfl
  rw [hk]
  unfold EvmYul.SpongeHash.Keccak256.keccak256Bytes
  generalize EvmYul.SpongeHash.Keccak256.absorbBlocks _ _ = st
  have hlt := squeezeBytes_lt st
  rw [foldl_norm _ 0 hlt]
  have := foldl_bytes_lt _ 0 hlt
  rw [squeezeBytes_length] at this
  unfold SolidCore.Solidity.Shared.norm SolidCore.Solidity.Shared.wordModulus
  have h2 : EvmYul.UInt256.size = 2 ^ 256 := rfl
  rw [h2]
  simpa using this

theorem wordToBytesBE_eq : ∀ (n v : Nat), SolidCore.Solidity.Source.wordToBytesBE n v =
    ((List.range n).reverse.map fun i => v / 256 ^ i % 256)
  | 0, _ => rfl
  | n + 1, v => by
    rw [SolidCore.Solidity.Source.wordToBytesBE, wordToBytesBE_eq n, List.range_succ_eq_map,
      List.reverse_cons, List.map_append, ← List.map_reverse, List.map_map]
    refine congrArg₂ _ ?_ ?_
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (256 ^ i)]
    · simp [SolidCore.Solidity.Source.normByte, SolidCore.Solidity.Shared.Account.byte]

/-- **SolidCore's mapping slot is the spec's.** -/
theorem solHash_eq (k s : Nat) :
    SolidCore.Refinement.Generic.solHash k s = keccakWord (wordBytes k ++ wordBytes s) := by
  unfold SolidCore.Refinement.Generic.solHash SolidCore.Solidity.Source.storageWordBytes
  rw [keccakWord_eq, wordToBytesBE_eq, wordToBytesBE_eq]
  rfl

/-! ## Mapping slots keyed by addresses

`SlotsSeparated m` names the one keccak256 assumption a spec over an address-keyed mapping at
slot `m` needs: keccak256 is separated (injective, every image at least `2 ^ 128`, so never a
small constant slot) on the preimages of `m[a]` for every address `a`
(`TrustedBase.KeccakSeparated`). It is not provable (keccak256 is not injective on all
inputs) and not refutable from the definitions; a theorem that uses it states it as a premise.
From it, SolidCore's slots of two addresses are equal only for equal addresses (`slot_inj`), and
none is a small slot (`slot_ge`). -/

theorem bytesWord_append (l : List Nat) (x : Nat) : bytesWord (l ++ [x]) = bytesWord l * 256 + x := by
  simp [bytesWord, List.foldl_append]

theorem bytesWord_wordToBytesBE : ∀ n v,
    bytesWord (SolidCore.Solidity.Source.wordToBytesBE n v) = v % 256 ^ n
  | 0, v => by simp [bytesWord, SolidCore.Solidity.Source.wordToBytesBE, Nat.mod_one]
  | n + 1, v => by
    rw [SolidCore.Solidity.Source.wordToBytesBE, bytesWord_append, bytesWord_wordToBytesBE n,
      Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    simp only [SolidCore.Solidity.Source.normByte, SolidCore.Solidity.Shared.Account.byte]
    omega

theorem bytesWord_wordBytes (v : Nat) : bytesWord (wordBytes v) = v % 2 ^ 256 := by
  have : wordBytes v = SolidCore.Solidity.Source.wordToBytesBE 32 v := by
    rw [wordToBytesBE_eq]; rfl
  rw [this, bytesWord_wordToBytesBE, show (256 : Nat) ^ 32 = 2 ^ 256 from rfl]

theorem length_wordBytes (v : Nat) : (wordBytes v).length = 32 := by simp [wordBytes]

/-- keccak256 is separated on the slots of `m[a]`, for every address `a`. -/
def SlotsSeparated (m : Nat) : Prop :=
  TrustedBase.KeccakSeparated (fun x => ∃ a < 2 ^ 160, x = TrustedBase.mappingPreimage a m)

theorem slot_inj {m : Nat} (h : SlotsSeparated m) {a b : Nat} (ha : a < 2 ^ 160) (hb : b < 2 ^ 160)
    (he : SolidCore.Refinement.Generic.solHash a m = SolidCore.Refinement.Generic.solHash b m) :
    a = b := by
  rw [solHash_eq, solHash_eq] at he
  have := h.1 _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ he
  unfold TrustedBase.mappingPreimage at this
  have hw := List.append_inj_left' this (by simp [length_wordBytes])
  have := congrArg bytesWord hw
  rw [bytesWord_wordBytes, bytesWord_wordBytes] at this
  omega

theorem slot_ge {m : Nat} (h : SlotsSeparated m) {a : Nat} (ha : a < 2 ^ 160) :
    2 ^ 128 ≤ SolidCore.Refinement.Generic.solHash a m := by
  rw [solHash_eq]
  exact h.2 _ ⟨a, ha, rfl⟩

end SolidCore.Spec
