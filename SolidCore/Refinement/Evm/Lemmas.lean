import EthLib.Execution.Proofs.Evm.Logic.Steps
import EthLib.Execution.Proofs.Evm.Logic.Symbolic

/-!
# EVM lemmas for the refinement proofs

Rules about EthLib's EVM that the bytecode proofs use and EthLib does not have
yet: PUSH0 as a Hoare triple, and how CALLDATALOAD and SHR read a selector and
an argument word out of call data.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts

namespace SolidCore.Refinement.Evm.Logic

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat} {stack : List U256}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {returnData : ByteArray}

/-- From Shanghai, PUSH0 pushes the word 0, for 2 gas (GA form). -/
theorem push0GA (hfork : .shapella ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    HoareGA fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (0 :: stack) memory (gas - 2) state substate returnData) := by
  apply At.ruleGA hlt hbyte
    (ofByte_of_decode (op := .push 0) rfl (by simpa [Op.since] using hfork)) (instruction_push 0)
    (runMono_pushN 0) (noAbort_pushN 0)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  have hlen : evm.stack.val.length < STACK_LIMIT := by rw [hst]; exact hstack
  rw [pushN_of_length_lt hlen]
  simp only [Fin.val_zero, ↓reduceIte]
  rw [show OPCODE_PUSH0 = 2 from rfl, charge_nat (by rw [hg]; exact hgas)]
  refine ⟨_, rfl, hcode, hj, hm, by simp [hpc], ?_, hmem, by simp [hg], hrun, herr, hout, hs, hss,
    hrd⟩
  simp [hst, pushData, bufferRead, bytesToNat]

/-- From Shanghai, PUSH0 pushes the word 0, for 2 gas. -/
theorem push0 (hfork : .shapella ≤ fork) (hlt : pc < code.size) (hbyte : code[pc] = 0x5f)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Hoare fork (At code message pc stack memory gas state substate returnData)
      (At code message (pc + 1) (0 :: stack) memory (gas - 2) state substate returnData) :=
  (push0GA hfork hlt hbyte hgas hstack).toG.toHoare

end SolidCore.Refinement.Evm.Logic

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
namespace SolidCore.Refinement.Evm

/-- A read of `a + b` bytes is the read of `a` bytes followed by the read of `b` more. -/
theorem bufferRead_add (data : ByteArray) (start a b : Nat) :
    bufferRead data start (a + b) = bufferRead data start a ++ bufferRead data (start + a) b := by
  simp [bufferRead, List.range_add, List.map_append, List.map_map, Function.comp_def,
    Nat.add_assoc]

/-- A read of `size` bytes past a prefix reads the suffix. -/
theorem bufferRead_append_size (pre b : ByteArray) (size : Nat) :
    bufferRead (pre ++ b) pre.size size = bufferRead b 0 size := by
  simp only [bufferRead]
  apply List.map_congr_left
  intro i _
  rw [byteAt_append, ite_eq_right (by omega), Nat.add_sub_cancel_left, Nat.zero_add]

/-- A read inside a prefix reads the prefix. -/
theorem bufferRead_append_of_le (pre b : ByteArray) {start size : Nat}
    (h : start + size ≤ pre.size) :
    bufferRead (pre ++ b) start size = bufferRead pre start size := by
  simp only [bufferRead]
  apply List.map_congr_left
  intro i hi
  rw [byteAt_append, ite_eq_left (by simp at hi; omega)]

/-- The 32 bytes of a word read back as the word. -/
theorem loadWord_wordBytes (w : U256) : loadWord (wordBytes w) 0 32 = w := by
  have hsize := size_wordBytes w
  rw [loadWord, ← hsize, bufferRead_zero_size]
  have bytes : (wordBytes w).data.toList = natToBytes 32 w.toNat :=
    EthLib.Base.U256.toList_toBeBytes w
  have small : w.toNat < 256 ^ 32 := by
    have := w.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  rw [bytes, EthLib.Base.bytesToNat_natToBytes_of_lt small]
  apply BitVec.eq_of_toNat_eq
  simp

/-- CALLDATALOAD right after a prefix, on call data that ends with a word, reads that word. -/
theorem loadWord_append_wordBytes (pre : ByteArray) (w : U256) :
    loadWord (pre ++ wordBytes w) pre.size 32 = w := by
  rw [loadWord, bufferRead_append_size, ← loadWord, loadWord_wordBytes]

/-- SHR by `8 * (32 - k)` of the word at offset 0 keeps the first `k` bytes of call data.

This is how a dispatcher reads its 4-byte selector. -/
theorem bitwiseShr_loadWord_zero (data : ByteArray) (k : Nat) (hk : k ≤ 32) (hk1 : 0 < k) :
    bitwiseShr (BitVec.ofNat 256 (8 * (32 - k))) (loadWord data 0 32) =
      BitVec.ofNat 256 (bytesToNat (bufferRead data 0 k)) := by
  have hsplit := bufferRead_add data 0 k (32 - k)
  rw [show k + (32 - k) = 32 by omega] at hsplit
  have hlt := bytesToNat_lt (bufferRead data 0 k)
  have hlt2 := bytesToNat_lt (bufferRead data (0 + k) (32 - k))
  simp only [bufferRead_length] at hlt hlt2
  have hsh : (BitVec.ofNat 256 (8 * (32 - k))).toNat = 8 * (32 - k) := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt
    have : 8 * (32 - k) ≤ 256 := by omega
    have : 256 < 2 ^ 256 := by decide
    omega
  have h256 : (256 : Nat) ^ k ≤ 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : (256 : Nat) ^ (32 - k) = 2 ^ (8 * (32 - k)) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  unfold bitwiseShr loadWord
  rw [hsh]
  rw [ite_eq_left (by omega), hsplit, bytesToNat_append, bufferRead_length]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, ← hpow]
  have hbig : bytesToNat (bufferRead data 0 k) * 256 ^ (32 - k) +
      bytesToNat (bufferRead data (0 + k) (32 - k)) < 2 ^ 256 := by
    have : (256 : Nat) ^ k * 256 ^ (32 - k) = 2 ^ 256 := by
      rw [← Nat.pow_add, show k + (32 - k) = 32 by omega]
    have := Nat.mul_le_mul_right (256 ^ (32 - k)) (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  rw [Nat.mod_eq_of_lt hbig, Nat.mod_eq_of_lt (by omega),
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hlt2, Nat.zero_add]

end SolidCore.Refinement.Evm
