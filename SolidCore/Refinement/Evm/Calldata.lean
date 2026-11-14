import SolidCore.Refinement.Evm.Lemmas
import SolidCore.Refinement.Abi

/-!
# ABI call data for the dirty-argument proofs

The call data of an external call with static arguments is a 4-byte selector
followed by one 32-byte word per argument. This module defines it, `cdOf`,
and the rules a symbolic run of a dispatcher needs on it: its size, the word
CALLDATALOAD reads at the offset of each argument, and the selector that
`SHR 224` of the first word gives.

It defines `Abi.Dirty` over the interface of `Abi.lean` (`Abi.calldata`,
`Abi.Param`, `Abi.Param.clean`) and restates cleanliness on bit vectors,
`cleanBv`, so `bv_decide` and `bv_omega` read it directly; `calldata_eq_cdOf`
and `not_cleanAllBv` carry a dirty call of the interface over to `cdOf`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm

namespace SolidCore.Refinement.Abi

/-- Some argument word is not clean for its parameter. -/
def Dirty (params : List Param) (args : List Nat) : Prop :=
  ∃ i, ∃ (hp : i < params.length) (ha : i < args.length), params[i].clean args[i] = false

/-- What a rejected call shows on both sides: failure, no output, no logs and the
call's initial storage. -/
def rejected (storage : List (Nat × Nat)) : Observable :=
  { success := false, output := [], logs := [], storage := slotValue storage }

end SolidCore.Refinement.Abi

namespace SolidCore.Refinement.Evm

/-! ## Call data -/

/-- The 32-byte words of `args`, one after another. -/
def wordsBytes : List U256 → ByteArray
  | [] => .empty
  | a :: rest => wordBytes a ++ wordsBytes rest

/-- The call data of a call with selector bytes `sel` and argument words `args`. -/
def cdOf (sel : ByteArray) (args : List U256) : ByteArray := sel ++ wordsBytes args

/-- The four big-endian bytes of a selector. -/
def selectorOf (s : Nat) : ByteArray := ⟨(natToBytes 4 s).toArray⟩

theorem size_selectorOf (s : Nat) : (selectorOf s).size = 4 := by
  simp [selectorOf, ByteArray.size, natToBytes_length]

theorem size_wordsBytes (args : List U256) : (wordsBytes args).size = 32 * args.length := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    simp only [wordsBytes, ByteArray.size_append, size_wordBytes, ih, List.length_cons]
    omega

theorem size_cdOf (sel : ByteArray) (args : List U256) :
    (cdOf sel args).size = sel.size + 32 * args.length := by
  simp [cdOf, ByteArray.size_append, size_wordsBytes]

/-- A read past a prefix reads the rest at the offset past it. -/
theorem bufferRead_append_add (pre b : ByteArray) (o size : Nat) :
    bufferRead (pre ++ b) (pre.size + o) size = bufferRead b o size := by
  simp only [bufferRead]
  apply List.map_congr_left
  intro i _
  rw [byteAt_append, ite_eq_right (by omega)]
  congr 1
  omega

/-- The `i`th word of `wordsBytes args` reads back as the `i`th argument. -/
theorem loadWord_wordsBytes (args : List U256) (i : Nat) (hi : i < args.length) :
    loadWord (wordsBytes args) (32 * i) 32 = args[i] := by
  induction args generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [wordsBytes, Nat.mul_zero, List.getElem_cons_zero]
      rw [loadWord, bufferRead_append_of_le _ _ (by simp [size_wordBytes]), ← loadWord,
        loadWord_wordBytes]
    | succ i =>
      simp only [wordsBytes, List.getElem_cons_succ]
      have h := bufferRead_append_add (wordBytes a) (wordsBytes rest) (32 * i) 32
      rw [size_wordBytes] at h
      rw [loadWord, show 32 * (i + 1) = 32 + 32 * i by omega, h, ← loadWord]
      exact ih i (by simp at hi; omega)

/-- CALLDATALOAD at the offset of argument `i` reads argument `i`. -/
theorem loadWord_cdOf (sel : ByteArray) (args : List U256) (i : Nat) (hi : i < args.length) :
    loadWord (cdOf sel args) (sel.size + 32 * i) 32 = args[i] := by
  rw [cdOf, loadWord, bufferRead_append_add, ← loadWord, loadWord_wordsBytes _ _ hi]

/-- CALLDATALOAD at any offset `n` of an argument word, in the form `simp` uses: the side
conditions are closed numerals once `sel.size` and `n` are. -/
theorem loadWord_cdOf_getD (sel : ByteArray) (args : List U256) (n : Nat)
    (hle : sel.size ≤ n) (hmod : (n - sel.size) % 32 = 0)
    (hlt : (n - sel.size) / 32 < args.length) :
    loadWord (cdOf sel args) n 32 = args.getD ((n - sel.size) / 32) 0 := by
  have hn : n = sel.size + 32 * ((n - sel.size) / 32) := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    ← loadWord_cdOf sel args _ hlt, ← hn]

/-- `SHR 224` of the first word of call data is its 4-byte selector. -/
theorem shr_cdOf (sel : ByteArray) (args : List U256) (hs : sel.size = 4) :
    bitwiseShr 224#256 (loadWord (cdOf sel args) 0 32) =
      BitVec.ofNat 256 (bytesToNat sel.data.toList) := by
  have h := bitwiseShr_loadWord_zero (cdOf sel args) 4 (by decide) (by decide)
  rw [show BitVec.ofNat 256 (8 * (32 - 4)) = 224#256 from rfl] at h
  rw [h, cdOf, bufferRead_append_of_le _ _ (by omega), ← hs, bufferRead_zero_size]

theorem bytesToNat_selectorOf (s : Nat) (hs : s < 2 ^ 32) :
    bytesToNat (selectorOf s).data.toList = s := by
  show bytesToNat (natToBytes 4 s).toArray.toList = s
  rw [List.toList_toArray]
  exact EthLib.Base.bytesToNat_natToBytes_of_lt (by simpa using hs)

/-- `SHR 224` of the first word of call data with selector `s` is `s`. -/
theorem shr_cdOf_selectorOf (s : Nat) (args : List U256) (hs : s < 2 ^ 32) :
    bitwiseShr 224#256 (loadWord (cdOf (selectorOf s) args) 0 32) = BitVec.ofNat 256 s := by
  rw [shr_cdOf _ _ (size_selectorOf s), bytesToNat_selectorOf s hs]

/-! ## Clean arguments, as bit vectors -/

/-- Whether `w` encodes a value of the parameter kind `p`, stated on bit vectors so that
`bv_decide` reads it. `cleanBv_iff` shows it agrees with `Abi.Param.clean`. -/
def cleanBv : Abi.Param → U256 → Prop
  | .uint bits, w => if bits < 256 then w < BitVec.ofNat 256 (2 ^ bits) else True
  | .int bits, w =>
    if 1 ≤ bits ∧ bits ≤ 256 then
      w < BitVec.ofNat 256 (2 ^ (bits - 1)) ∨ BitVec.ofNat 256 (2 ^ 256 - 2 ^ (bits - 1)) ≤ w
    else Abi.Param.clean (.int bits) w.toNat = true
  | .bool, w => w < 2#256
  | .enum n, w => if n < 2 ^ 256 then w < BitVec.ofNat 256 n else True

/-- Whether every word of `ws` is clean for its parameter in `ps`, as bit vectors. -/
def cleanAllBv : List Abi.Param → List U256 → Prop
  | p :: ps, w :: ws => cleanBv p w ∧ cleanAllBv ps ws
  | _, _ => True

theorem cleanBv_iff (p : Abi.Param) (w : U256) : cleanBv p w ↔ p.clean w.toNat = true := by
  have hw := w.isLt
  cases p with
  | uint bits =>
    simp only [cleanBv, Abi.Param.clean, decide_eq_true_eq]
    split
    · rename_i hb
      have : 2 ^ bits < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hb
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
    · rename_i hb
      have : 2 ^ 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega)
      simp only [true_iff]; omega
  | int bits =>
    simp only [cleanBv]
    split
    · rename_i hb
      have h1 : 2 ^ (bits - 1) ≤ 2 ^ 255 := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
      have h3 : 0 < 2 ^ (bits - 1) := Nat.two_pow_pos _
      simp only [Abi.Param.clean, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · exact Iff.rfl
  | bool =>
    simp only [cleanBv, Abi.Param.clean, decide_eq_true_eq, BitVec.lt_def]
    rfl
  | enum n =>
    simp only [cleanBv, Abi.Param.clean, decide_eq_true_eq]
    split
    · rename_i hn
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    · simp only [true_iff]; omega

/-- The call data of `Abi.calldata` is `cdOf` on the argument words. -/
theorem calldata_eq_cdOf (sel : Nat) (args : List Nat) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Abi.calldata sel args = cdOf (selectorOf sel) (args.map (BitVec.ofNat 256)) := by
  have hw : ∀ (ws : List Nat), (∀ a ∈ ws, a < 2 ^ 256) →
      (wordsBytes (ws.map (BitVec.ofNat 256))).data.toList = ws.flatMap (natToBytes 32) := by
    intro ws
    induction ws with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro h
      simp only [List.map_cons, wordsBytes, ByteArray.data_append, Array.toList_append,
        List.flatMap_cons]
      have bytes : (wordBytes (BitVec.ofNat 256 a)).data.toList =
          natToBytes 32 (BitVec.ofNat 256 a).toNat :=
        EthLib.Base.U256.toList_toBeBytes _
      rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), bytes, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (h a List.mem_cons_self)]
  apply ByteArray.ext
  apply Array.ext'
  simp only [Abi.calldata, cdOf, selectorOf, ByteArray.data_append, Array.toList_append,
    List.toList_toArray]
  rw [hw args hargs]

/-- A dirty argument list gives argument words that are not all clean. -/
theorem not_cleanAllBv (ps : List Abi.Param) (args : List Nat)
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (hd : Abi.Dirty ps args) :
    ¬ cleanAllBv ps (args.map (BitVec.ofNat 256)) := by
  obtain ⟨i, hp, ha, hc⟩ := hd
  induction ps generalizing args i with
  | nil => simp at hp
  | cons p ps ih =>
    cases args with
    | nil => simp at ha
    | cons a args =>
      intro hcl
      simp only [List.map_cons, cleanAllBv] at hcl
      cases i with
      | zero =>
        have := (cleanBv_iff p _).mp hcl.1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hargs a List.mem_cons_self)] at this
        simp at hc
        rw [this] at hc
        exact absurd hc (by simp)
      | succ i =>
        exact ih args (fun b hb => hargs b (List.mem_cons_of_mem _ hb)) i
          (by simp at hp; omega) (by simp at ha; omega) (by simpa using hc) hcl.2

end SolidCore.Refinement.Evm


