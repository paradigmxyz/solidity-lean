import SolidCore.Refinement.Keccak.Agree
import SolidCore.Refinement.Generic.Event
import SolidCore.Refinement.Generic.MirRun
import EthLib.Execution.Evm.Instructions.Keccak

/-!
# EthLib's KECCAK256 of two words is SolidCore's mapping-slot hash

The KECCAK256 word EthLib pushes for the 64 bytes of two words (\`Generic.wordBytes\`, big-endian)
is SolidCore's \`Generic.solHash\` of them, reduced to a word: the 64-byte agreement of the two
Keccak-256 implementations (Agree.lean, \`keccak256_64\`), with both sides reading the digest as a
big-endian number. It holds for every pair of numbers; a word's bytes keep its low 256 bits.
-/

namespace SolidCore.Refinement.Keccak

open SolidCore.Solidity.Source

/-- The bytes of two words, as EthLib's memory holds them, are SolidCore's storage bytes. -/
theorem twoWords_bytes (a b : Nat) :
    ((Generic.wordBytes a ++ Generic.wordBytes b).map UInt8.ofBitVec).map UInt8.toNat =
      storageWordBytes a ++ storageWordBytes b := by
  have h (v : BitVec 8) : (UInt8.ofBitVec v).toNat = v.toNat := rfl
  simp [Generic.wordBytes, storageWordBytes, Generic.evWordToBytesBE_eq, wordBytes, Function.comp_def, h]

/-- EthLib's word of 32 bytes, big-endian. -/
theorem fromBeBytes_toNat (v : Vector UInt8 32) :
    (EthLib.Base.U256.fromBeBytes v).toNat = EthLib.Base.bytesToNat v.toList % 2 ^ 256 := by
  simp only [EthLib.Base.U256.fromBeBytes, BitVec.toNat_ofNat]

/-- SolidCore's word of a list of bytes is EthLib's, reduced to a word. -/
theorem bytesToWordBE_map (l : List UInt8) :
    bytesToWordBE (l.map UInt8.toNat) = EthLib.Base.bytesToNat l % 2 ^ 256 := by
  have hb (b : UInt8) : b.toNat % 256 = b.toNat := Nat.mod_eq_of_lt b.toNat_lt
  have hw : SolidCore.Solidity.Shared.wordModulus = 2 ^ 256 := rfl
  simp only [bytesToWordBE, SolidCore.Solidity.Shared.norm, hw, List.foldl_map, normByte,
    SolidCore.Solidity.Shared.Account.byte, hb, EthLib.Base.bytesToNat]

/-- **EthLib's Keccak-256 of the 64 bytes of two words is SolidCore's mapping-slot hash**. -/
theorem ethKeccak_twoWords (a b : Nat) :
    (EthLib.Execution.Evm.keccak
      ⟨((Generic.wordBytes a ++ Generic.wordBytes b).map UInt8.ofBitVec).toArray⟩).toNat =
      Generic.solHash a b % 2 ^ 256 := by
  have hlen : ((Generic.wordBytes a ++ Generic.wordBytes b).map UInt8.ofBitVec).length = 64 := by
    simp [Generic.wordBytes]
  rw [Generic.solHash, keccakWord, ← twoWords_bytes,
    show Keccak.keccak256Bytes = EvmYul.SpongeHash.Keccak256.keccak256Bytes from rfl, keccak256_64 _ hlen,
    bytesToWordBE_map, Nat.mod_mod, EthLib.Execution.Evm.keccak]
  exact fromBeBytes_toNat _

#print axioms ethKeccak_twoWords

end SolidCore.Refinement.Keccak
