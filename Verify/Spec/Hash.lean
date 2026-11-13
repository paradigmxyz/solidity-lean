import Verify.Spec.Semantics
import SolidCore.Refinement.Generic.Source

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

end SolidCore.Spec
