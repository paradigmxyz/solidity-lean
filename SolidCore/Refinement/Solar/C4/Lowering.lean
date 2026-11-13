import Verify.C4
import SolidCore.Refinement.Spec
import SolidCore.Refinement.Evm.WideStorage
import W1Proofs.Tactic
import c4.gen.Main.Stage0

/-!
# c4: SolidCore to solar's first lowered MIR, and on to its bytecode

The source stage of the corpus contract c4 (scripts/refinement/corpus/c4.sol),

    contract Main { uint8 v; uint8 w = 7;
      function add(uint8 x) external returns (uint8) { v += x; w ^= x; return v; } }

from SolidCore's checked contract (Corpus.C4.contract?) to the first lowered MIR module solar
compiles for it (SolarTV.Export.Main.stage0, after lower-evm-shaped, so lower-abi's ABI
decoding and lower-dispatch's dispatcher included; c4.gen.Main.Stage0, solar's export in
solar-tv/milestone/c4), in SolarTV's
lowered MIR semantics under any oracle. Here the MIR side is a symbolic run of this one module;
C4/LoweringGeneric.lean derives the same stage, and the one from any storage that writes slot 0,
from the generic source stage.

* mir_run_of: on every call whose call data reads as add(x) with a clean x < 2 ^ 8, no value,
  from the deployed storage (slot 0 = 7 * 256), stage0 returns x and leaves slot 0 holding
  x + (7 ^ x) * 256, by W1Proofs.Tactic's evaluation steps; the packed words are checked by
  the kernel on every clean x (slot_word, low_byte: Evm.Wide.forall_of_lt_ofNat and
  decide +kernel). mir_run_dirty_of: a dirty word reverts with empty data.
* mir_run: both, as expectedAt Verify.C4.deployed x, the observable of Verify.C4.model.
* lowering: the stage on Verify.C4.scope, every call of add on any argument word from the
  deployed storage, with source_run (Verify.C4.run_add).
* mir_run_at: from any storage σ, on a symbolic slot-0 word, stage0 runs to expectedAt σ x,
  clean or dirty, v + x in uint8 or a Panic(0x11) revert (mir_run_ok_of, mir_run_panic_of).
  stage0's packed-word operations are computed through toNat for every slot-0 word
  (slot_word_at, from Nat.testBit lemmas on the masks), not by the kernel's enumeration.
* loweringAt_of_runs: the stage on Verify.C4.scopeAt, any storage that writes slot 0, from
  SolidCore's run there (source_run_at, Verify.C4.run_add_at) and a MIR module's run there
  (hmir). loweringAt: the stage for stage0, with hmir from mir_run_at.
* target_run_at: EthLib runs solar's bytecode Corpus.C4.code from any storage to the same
  observable, by Evm.WideStorage's steps on a named slot-0 word (tgt_slot_word). mir_assemblyAt:
  the assembly-side stage from stage0 to the bytecode on scopeAt; certifiedAt: Verify.C4.postAt
  of the bytecode on scopeAt through loweringAt and mir_assemblyAt; certifiedAt_of_backend: the
  same through any backend stage to EVM IR; bytecode_satisfiesAll: postAt of the bytecode on
  every call from every storage (scopeAll), slot 0 written or not, which SolidCore cannot give
  since it runs a call from its storage written over the constructor's (slot 0 = 7 * 256).
* certified_of_backend: Verify.C4's specification holds of solar's bytecode Corpus.C4.code
  through the stages, given the backend stage from stage0 to the final EVM IR (solar-tv's
  SolarTV.Milestone.C4.c4_mir_to_evmir; C4/Certified.lean composes the three stages). The assembly
  stage is derived from c4's direct refinement Corpus.C4.refines_full (assembly_of_refines),
  not from the EVM IR.

The names of solar's stages (SolarTV.Export.Main) are those of w1's and w4's too, so this
module cannot share an import closure with Solar.Lowering, Solar.W4Lowering or the library
root; lake build SolidCoreSolarC4 builds it.

No sorry, native_decide or bv_decide: the theorems depend on propext, Quot.sound and
Classical.choice only (pinned below).
-/

namespace SolidCore.Refinement.Solar.C4

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide

/-- The selector of add(uint8). -/
abbrev addSelector : Nat := Bytecode.C4.Main.addSelector

/-- What add(x) from the storage σ shows: the observable of Verify.C4.model. -/
def expectedAt (σ : List (Nat × Nat)) (x : U256) : Observable :=
  Verify.observe (slotValue σ) (Verify.C4.model [x.toNat] (slotValue σ))

/-! ## The calls of the scope -/

theorem scopeAt_callAt {call : Call} (h : Verify.C4.scopeAt call) :
    ∃ (x : U256) (σ : List (Nat × Nat)), (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) ∧
      call = callAt addSelector [x] σ := by
  obtain ⟨σ, hσ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [Corpus.C4.fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, σ, hσ, ?_⟩
    have ha : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callAt, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha]

theorem scope_callAt {call : Call} (h : Verify.C4.scope call) :
    ∃ x : U256, call = callAt addSelector [x] Verify.C4.deployed := by
  obtain ⟨fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [Corpus.C4.fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, ?_⟩
    have ha : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callAt, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha]

/-! ## SolidCore -/

/-- SolidCore runs c4's add on any argument word, from any storage σ that writes slot 0, to
expectedAt σ x. -/
theorem source_run_at {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) (x : U256) (σ : List (Nat × Nat))
    (hσ : ∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) :
    Source.run Corpus.C4.fuel c (callAt addSelector [x] σ) = some (expectedAt σ x) := by
  obtain ⟨hk, _, hdep⟩ := Verify.C4.shape_of hc
  obtain ⟨d, hd⟩ := deployedAt_of hdep
  exact Verify.C4.run_add_at hk hd x σ hσ

/-! ## Call data -/

section Calldata

open SolarTV SolarTV.Machine

theorem shl_or_ofNat (acc b : Nat) (hb : b < 256) :
    (BitVec.ofNat 256 acc <<< 8) ||| BitVec.ofNat 256 b = BitVec.ofNat 256 (acc * 256 + b) := by
  have hand : (BitVec.ofNat 256 acc <<< 8) &&& BitVec.ofNat 256 b = 0 := by
    ext i hi
    rw [BitVec.getElem_and, BitVec.getElem_shiftLeft, ← BitVec.getLsbD_eq_getElem,
      ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
    by_cases h8 : i < 8
    · simp [h8]
    · have : b.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
          (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt h8)))
      simp [BitVec.getLsbD_ofNat, this]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem foldl_word (data : ByteArray) (off : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun (acc : BitVec 256) i =>
        (acc <<< 8) ||| BitVec.ofNat 256 (data.data.getD (off + i) 0).toNat)
        (BitVec.ofNat 256 acc) =
      BitVec.ofNat 256 (l.foldl (fun acc i => acc * 256 + (byteAt data (off + i)).toNat) acc)
  | [], _ => rfl
  | i :: l, acc => by
    simp only [List.foldl_cons]
    have hget : (data.data.getD (off + i) 0) = byteAt data (off + i) := rfl
    rw [hget, shl_or_ofNat _ _ (byteAt data (off + i)).toNat_lt, foldl_word data off l]

/-- CALLDATALOAD in SolarTV is EthLib's: the big-endian word of 32 bytes of call data from the
offset, zero past its end. -/
theorem calldataWord_eq (call : Call) (off : BitVec 256) :
    calldataWord call off = loadWord call.calldata off.toNat 32 := by
  unfold calldataWord loadWord bufferRead bytesToNat
  rw [show (0 : BitVec 256) = BitVec.ofNat 256 0 from rfl, foldl_word, List.foldl_map]

theorem calldata_callAt (x : U256) (σ : List (Nat × Nat)) :
    (callAt addSelector [x] σ).calldata = cdOf (selectorOf addSelector) [x] := by
  have := calldata_eq_cdOf addSelector [x.toNat] (by
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl
    exact BitVec.isLt _)
  simpa [callAt, List.map_map, Function.comp_def] using this

theorem word0 (x : U256) (σ : List (Nat × Nat)) :
    EvmRules.Evm.shr 224 (calldataWord (callAt addSelector [x] σ) 0) = BitVec.ofNat 256 addSelector := by
  rw [calldataWord_eq, calldata_callAt]
  have := shr_cdOf_selectorOf addSelector [x] (by decide)
  simpa [EvmRules.Evm.shr, bitwiseShr] using this

theorem word4 (x : U256) (σ : List (Nat × Nat)) : calldataWord (callAt addSelector [x] σ) 4 = x := by
  rw [calldataWord_eq, calldata_callAt]
  exact loadWord_cdOf_getD _ [x] 4 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem word0' (x : U256) (σ : List (Nat × Nat)) :
    EvmRules.Evm.shr 224 (calldataWord (callAt addSelector [x] σ) 0) = 33980010 := by
  have h := word0 x σ
  rw [show BitVec.ofNat 256 addSelector = 33980010 from rfl] at h
  exact h

theorem size_callAt (x : U256) (σ : List (Nat × Nat)) :
    (callAt addSelector [x] σ).calldata.size = 36 := by
  rw [calldata_callAt, size_cdOf, size_selectorOf]; rfl

end Calldata

/-! ## SolarTV's lowered MIR runs stage0 from the deployed storage -/

section Lowering

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

theorem bytes_toNat (len n : Nat) :
    (List.range len).map (fun i => (n / 256 ^ (len - 1 - i)) % 256) =
      (natToBytes len n).map (·.toNat) := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih =>
    rw [natToBytes_succ, List.map_append, ← ih, List.range_succ, List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · simp

theorem byte_toNat (v : EvmRules.Word) (i : Nat) (_hi : i < 32) :
    (SolarTV.Memory.byte v i).toNat = v.toNat / 256 ^ (31 - i) % 256 := by
  unfold SolarTV.Memory.byte
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem read_store (m : Mem) (v : EvmRules.Word) :
    (((m.store 0 v).expand 0 32).read 0 32).map BitVec.toNat =
      (natToBytes 32 v.toNat).map (·.toNat) := by
  rw [← bytes_toNat]
  simp only [Mem.read, Mem.expand, Mem.store, List.map_map]
  simp only [show (32 = 0) = False from by decide, ite_false]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, Nat.zero_add, Nat.zero_le, true_and, hi, ite_true, Nat.sub_zero]
  rw [byte_toNat v i hi]

theorem gt_255 (x : EvmRules.Word) (hx : x.toNat < 256) : EvmRules.Evm.gt x 255 = 0 := by
  have : (255#256).ult x = false := by simp [BitVec.ult]; omega
  simp [EvmRules.Evm.gt, this]

/-- What add(x) shows from the deployed storage, on a clean x: x returned, x + (7 ^ x) * 256
in slot 0. -/
def expectedD (x : EvmRules.Word) : Observable :=
  { success := true, output := SolidCore.Verify.word x.toNat, logs := [],
    storage := fun k => if k % 2 ^ 256 = 0 then x.toNat + (7 ^^^ x.toNat) * 256
      else slotValue [(0, 1792)] k }

/-- The word add writes to slot 0 from the deployed storage, for each clean x, by the kernel's
evaluation on every x below 256. -/
theorem slot_word : ∀ x : EvmRules.Word, x.toNat < 256 →
    EvmRules.Evm.or
      (EvmRules.Evm.and
        (EvmRules.Evm.or
          (EvmRules.Evm.and 1792 115792089237316195423570985008687907853269984665640564039457584007913129639680) x)
        115792089237316195423570985008687907853269984665640564039457584007913129574655)
      (EvmRules.Evm.shl 8
        (EvmRules.Evm.xor
          (EvmRules.Evm.byte 30
            (EvmRules.Evm.or
              (EvmRules.Evm.and 1792
                115792089237316195423570985008687907853269984665640564039457584007913129639680) x)) x)) =
      BitVec.ofNat 256 (x.toNat + (7 ^^^ x.toNat) * 256) :=
  SolidCore.Refinement.Evm.Wide.forall_of_lt_ofNat (by decide +kernel)

theorem low_byte : ∀ x : EvmRules.Word, x.toNat < 256 →
    EvmRules.Evm.and (BitVec.ofNat 256 (x.toNat + (7 ^^^ x.toNat) * 256)) 255 = x :=
  SolidCore.Refinement.Evm.Wide.forall_of_lt_ofNat (by decide +kernel)

/-- The operands of commutative word operations in the order `sym_cond` puts them in (its
`word*Comm` simprocs), so that facts about them match the goal. -/
syntax "comm_order" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| comm_order $[$loc]?) => `(tactic| simp only [SolarTV.Milestone.W1.wordAddComm,
      SolarTV.Milestone.W1.wordMulComm, SolarTV.Milestone.W1.wordAndComm,
      SolarTV.Milestone.W1.wordOrComm, SolarTV.Milestone.W1.wordXorComm] $[$loc]?)

set_option linter.unusedSimpArgs false in
theorem mir_run_of (o : Oracle) (call : Call) (x : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 33980010)
    (h4 : calldataWord call 4 = x) (hx : x.toNat < 256) (hst : call.storage = [(0, 1792)]) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 12).map (fun r => observe call r.2 r.1) = some (expectedD x) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  have hs0 : (State.initial call).storage 0 = 1792 := by simp [State.initial, hst, slotValue]
  have hgt := gt_255 x hx
  have ha : EvmRules.Evm.and 1792 255 = 0 := by decide
  have hadd : EvmRules.Evm.add 0 x = x := by simp [EvmRules.Evm.add]
  have hlt : ¬ (255 : EvmRules.Word) < x := by simp [BitVec.lt_def]; omega
  try comm_order at ha hadd
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, hs0, hgt, ha, hadd, hlt])
  have hsw := slot_word x hx
  have hlb := low_byte x hx
  -- `sym_eval` folds the constant `and 1792 mask` in the goal: fold it in the lemma too.
  try dsimp only [SolarTV.Milestone.W1.foldAnd] at hsw
  try comm_order at hsw hlb
  rw [hsw]
  try comm_order
  rw [hlb]
  simp only [observe, expectedD, Option.some.injEq, Observable.mk.injEq, true_and]
  refine ⟨?_, rfl, ?_⟩
  · exact read_store _ x
  · funext slot
    simp only [storageOf, update]
    have hv : x.toNat + (7 ^^^ x.toNat) * 256 < 2 ^ 256 := by
      have := Nat.xor_lt_two_pow (n := 8) (x := 7) (y := x.toNat) (by decide) (by omega)
      omega
    split
    · rename_i e
      have h : slot % 2 ^ 256 = 0 := by simpa using congrArg BitVec.toNat e
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    · rename_i e
      have h : ¬ slot % 2 ^ 256 = 0 :=
        fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      simp only [State.initial, hst, BitVec.toNat_ofNat]
      exact slotValue_mod_mod _ slot

set_option linter.unusedSimpArgs false in
/-- On a dirty word, stage0 reverts with empty data and keeps the storage. -/
theorem mir_run_dirty_of (o : Oracle) (call : Call) (x : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 33980010)
    (h4 : calldataWord call 4 = x) (hx : ¬ x.toNat < 256) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 12).map
        (fun r => observe call r.2 r.1) =
      some ⟨false, [], [], slotValue call.storage⟩ := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  have hgt : EvmRules.Evm.gt x 255 = 1 := by
    have : (255#256).ult x = true := by simp [BitVec.ult]; omega
    simp [EvmRules.Evm.gt, this]
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, hgt])
  rfl

/-- A run of a lowered MIR module that ends within some fuel is its fuel-free result. -/
theorem mir_sem_of_run {o : Oracle} {m : MIR.Lowered.Module} {call : Call} {obs : Observable}
    (n : Nat) (h : (MIR.Lowered.Module.run o m call n).map (fun r => observe call r.2 r.1) = some obs) :
    (MIR.Lowered.moduleSem o).run m call = some obs := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  have e : MIR.Lowered.moduleLayer.result o m call = some r :=
    MIR.Lowered.moduleLayer.result_of_ends ⟨n, hr⟩
  show (MIR.Lowered.moduleLayer.result o m call).map _ = _
  rw [e]
  rfl

/-- SolarTV's lowered MIR semantics runs c4's first lowered MIR module on every call of add(x)
from the deployed storage, under every oracle, to expectedAt Verify.C4.deployed x. -/
theorem mir_run (o : Oracle) (x : U256) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0
        (callAt addSelector [x] Verify.C4.deployed) = some (expectedAt Verify.C4.deployed x) := by
  by_cases hx : x.toNat < 256
  · refine mir_sem_of_run 12 ((mir_run_of o _ x rfl (size_callAt x _) (word0' x _) (word4 x _) hx
      rfl).trans ?_)
    have h2 : slotValue Verify.C4.deployed 0 % 256 + x.toNat < 256 := by
      simp [slotValue, Verify.C4.deployed]; omega
    simp only [expectedAt, Verify.C4.model_ok x.toNat _ hx h2, Verify.observe, expectedD,
      Option.some.injEq, Observable.mk.injEq, true_and]
    have h0 : slotValue Verify.C4.deployed 0 = 1792 := rfl
    refine ⟨by rw [h0]; simp, ?_⟩
    funext k
    have hv : x.toNat + (7 ^^^ x.toNat) * 256 < 2 ^ 256 := by
      have := Nat.xor_lt_two_pow (n := 8) (x := 7) (y := x.toNat) (by decide) (by omega)
      omega
    rw [h0]
    split
    · simp only [Nat.reduceDiv, Nat.reduceMod, Nat.zero_mul, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rfl
  · refine mir_sem_of_run 12 ((mir_run_dirty_of o _ x rfl (size_callAt x _) (word0' x _)
      (word4 x _) hx).trans ?_)
    simp only [expectedAt, Verify.C4.model_dirty x.toNat _ hx, Verify.observe]
    rfl

end Lowering

/-! ## SolarTV's lowered MIR runs stage0 from any storage

On a symbolic slot-0 word s, stage0's packed-word operations are computed through toNat: the
masks are multiples of powers of two with their bits counted by Nat.testBit (and_mask_high,
and_mask_byte1), and an OR of words with disjoint bits is their sum (toNat_or_disjoint,
or_byte1), so slot_word_at gives the word add writes, s's high bytes, w ^ x in byte 1 and v + x
in byte 0, for every s. -/

section Packed

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

/-- Masking a word below 2 ^ (k + w) with its bits from k up keeps the multiple of 2 ^ k below it. -/
theorem and_mask_high (n k w : Nat) (hn : n < 2 ^ (k + w)) :
    n &&& 2 ^ k * (2 ^ w - 1) = n / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : k ≤ j
  · rw [Nat.sub_add_cancel hj]
    by_cases hw : j < k + w
    · simp [hj, show j - k < w by omega]
    · have : n.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hj]

/-- Masking a word with every bit but those of byte 1 clears byte 1. -/
theorem and_mask_byte1 (n : Nat) (hn : n < 2 ^ 256) :
    n &&& (2 ^ 16 * (2 ^ 240 - 1) + (2 ^ 8 - 1)) = 2 ^ 16 * (n / 2 ^ 16) + n % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : 2 ^ 8 - 1 < 2 ^ 16 := by decide
  have h2 : n % 2 ^ 8 < 2 ^ 16 := by omega
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
  by_cases hj : j < 16
  · simp only [hj, ite_true, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases h8 : j < 8 <;> simp [h8]
  · simp only [hj, ite_false, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
    rw [Nat.sub_add_cancel (by omega)]
    by_cases hw : j < 256
    · simp [show j - 16 < 240 by omega]
    · have : n.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]

/-- A byte y placed in byte 1 of a word whose byte 1 is clear is added to it. -/
theorem or_byte1 (H c y : Nat) (hc : c < 2 ^ 8) (hy : y < 2 ^ 8) :
    (2 ^ 16 * H + c) ||| 2 ^ 8 * y = 2 ^ 16 * H + (2 ^ 8 * y + c) := by
  have h1 : c < 2 ^ 16 := by omega
  have h2 : 2 ^ 8 * y + c < 2 ^ 16 := by omega
  rw [Nat.two_pow_add_eq_or_of_lt h1, Nat.two_pow_add_eq_or_of_lt h2, Nat.two_pow_add_eq_or_of_lt hc,
    Nat.or_assoc, Nat.or_comm c]

/-- AND with 255 keeps the low byte. -/
theorem toNat_and_255 (s : EvmRules.Word) : (EvmRules.Evm.and s 255).toNat = s.toNat % 256 := by
  unfold EvmRules.Evm.and
  rw [BitVec.toNat_and, show (255 : EvmRules.Word).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- AND with the mask that clears v's byte keeps every byte above it. -/
theorem toNat_and_high (s : EvmRules.Word) :
    (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129639680).toNat =
      s.toNat / 256 * 256 := by
  unfold EvmRules.Evm.and
  rw [BitVec.toNat_and, show (115792089237316195423570985008687907853269984665640564039457584007913129639680 : EvmRules.Word).toNat = 2 ^ 8 * (2 ^ 248 - 1) from rfl,
    and_mask_high _ 8 248 s.isLt]
  rfl

/-- AND with the mask that clears w's byte keeps every other byte. -/
theorem toNat_and_byte1 (s : EvmRules.Word) :
    (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129574655).toNat =
      s.toNat / 65536 * 65536 + s.toNat % 256 := by
  unfold EvmRules.Evm.and
  rw [BitVec.toNat_and, show (115792089237316195423570985008687907853269984665640564039457584007913129574655 : EvmRules.Word).toNat = 2 ^ 16 * (2 ^ 240 - 1) + (2 ^ 8 - 1) from rfl,
    and_mask_byte1 _ s.isLt]
  omega

/-- BYTE 30 reads byte 1 from the low end, w's. -/
theorem toNat_byte30 (v : EvmRules.Word) : (EvmRules.Evm.byte 30 v).toNat = v.toNat / 256 % 256 := by
  unfold EvmRules.Evm.byte
  rw [show (30 : EvmRules.Word).ult 32 = true from rfl, Bool.cond_true, show ((31 : EvmRules.Word) - 30) * 8 = 8 from rfl,
    BitVec.ushiftRight_eq', BitVec.toNat_and, BitVec.toNat_ushiftRight, show (255 : EvmRules.Word).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rfl

/-- SHL 8 of a byte places it in byte 1. -/
theorem toNat_shl8 (v : EvmRules.Word) (hv : v.toNat < 256) : (EvmRules.Evm.shl 8 v).toNat = v.toNat * 256 := by
  unfold EvmRules.Evm.shl
  rw [show (8 : EvmRules.Word).ult 256 = true from rfl, Bool.cond_true, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [show (8 : EvmRules.Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- OR of a multiple of 2 ^ k and a word below 2 ^ k is their sum. -/
theorem toNat_or_disjoint (a b : EvmRules.Word) (k : Nat) (ha : a.toNat % 2 ^ k = 0) (hb : b.toNat < 2 ^ k) :
    (EvmRules.Evm.or a b).toNat = a.toNat + b.toNat := by
  unfold EvmRules.Evm.or
  rw [BitVec.toNat_or]
  have : a.toNat = 2 ^ k * (a.toNat / 2 ^ k) := by
    have := Nat.div_add_mod a.toNat (2 ^ k); omega
  rw [this, ← Nat.two_pow_add_eq_or_of_lt hb]

/-- v + x, when it fits in uint8, does not wrap. -/
theorem toNat_add_low (s x : EvmRules.Word) (hc : s.toNat % 256 + x.toNat < 256) :
    (EvmRules.Evm.add (EvmRules.Evm.and s 255) x).toNat = s.toNat % 256 + x.toNat := by
  unfold EvmRules.Evm.add
  rw [BitVec.toNat_add, toNat_and_255]
  exact Nat.mod_eq_of_lt (by omega)

/-- The word add writes to slot 0 from any slot-0 word s, when v + x fits in uint8: s's high
bytes, w ^ x in byte 1 and v + x in byte 0. -/
theorem slot_word_at (s x : EvmRules.Word) (hx : x.toNat < 256) (hc : s.toNat % 256 + x.toNat < 256) :
    (EvmRules.Evm.or
      (EvmRules.Evm.and
        (EvmRules.Evm.or
          (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129639680)
          (EvmRules.Evm.add (EvmRules.Evm.and s 255) x))
        115792089237316195423570985008687907853269984665640564039457584007913129574655)
      (EvmRules.Evm.shl 8
        (EvmRules.Evm.xor
          (EvmRules.Evm.byte 30
            (EvmRules.Evm.or
              (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129639680)
              (EvmRules.Evm.add (EvmRules.Evm.and s 255) x)))
          x))).toNat =
      s.toNat / 65536 * 65536 + (s.toNat / 256 % 256 ^^^ x.toNat) * 256 + (s.toNat % 256 + x.toNat) := by
  have h34 := toNat_add_low s x hc
  have h11 : (EvmRules.Evm.or
      (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129639680)
      (EvmRules.Evm.add (EvmRules.Evm.and s 255) x)).toNat = s.toNat / 256 * 256 + (s.toNat % 256 + x.toNat) := by
    rw [toNat_or_disjoint _ _ 8 (by rw [toNat_and_high]; omega) (by rw [h34]; omega),
      toNat_and_high, h34]
  generalize EvmRules.Evm.or
      (EvmRules.Evm.and s 115792089237316195423570985008687907853269984665640564039457584007913129639680)
      (EvmRules.Evm.add (EvmRules.Evm.and s 255) x) = v at h11 ⊢
  have hy : (EvmRules.Evm.xor (EvmRules.Evm.byte 30 v) x).toNat = s.toNat / 256 % 256 ^^^ x.toNat := by
    unfold EvmRules.Evm.xor
    rw [BitVec.toNat_xor, toNat_byte30, h11]
    congr 1
    omega
  have hylt : s.toNat / 256 % 256 ^^^ x.toNat < 2 ^ 8 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  generalize EvmRules.Evm.xor (EvmRules.Evm.byte 30 v) x = y at hy ⊢
  unfold EvmRules.Evm.or
  rw [BitVec.toNat_or, toNat_and_byte1, toNat_shl8 y (by omega), h11, hy]
  rw [show (s.toNat / 256 * 256 + (s.toNat % 256 + x.toNat)) / 65536 * 65536 +
      (s.toNat / 256 * 256 + (s.toNat % 256 + x.toNat)) % 256 =
      2 ^ 16 * (s.toNat / 65536) + (s.toNat % 256 + x.toNat) by omega,
    show (s.toNat / 256 % 256 ^^^ x.toNat) * 256 = 2 ^ 8 * (s.toNat / 256 % 256 ^^^ x.toNat) by omega,
    or_byte1 _ _ _ (by omega) hylt]
  omega

/-- The low byte of that word is v + x, which add returns. -/
theorem low_byte_at (s x : EvmRules.Word) (hc : s.toNat % 256 + x.toNat < 256) :
    EvmRules.Evm.and (BitVec.ofNat 256
        (s.toNat / 65536 * 65536 + (s.toNat / 256 % 256 ^^^ x.toNat) * 256 + (s.toNat % 256 + x.toNat))) 255 =
      BitVec.ofNat 256 (s.toNat % 256 + x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_255, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := s.isLt
  have hy : s.toNat / 256 % 256 ^^^ x.toNat < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  omega

set_option linter.unusedSimpArgs false in
/-- On a clean x where v + x fits in uint8, from any storage, stage0 runs as Verify.C4.model:
v + x returned, and slot 0 holding the high bytes of the call's slot-0 word, w ^ x and
v + x. -/
theorem mir_run_ok_of (o : Oracle) (call : Call) (x : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 33980010)
    (h4 : calldataWord call 4 = x) (hx : x.toNat < 256)
    (hc : slotValue call.storage 0 % 256 + x.toNat < 256) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 12).map (fun r => observe call r.2 r.1) =
      some (SolidCore.Verify.observe (slotValue call.storage)
        (SolidCore.Verify.C4.model [x.toNat] (slotValue call.storage))) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  have hgt := gt_255 x hx
  have hs : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    show (BitVec.ofNat 256 (slotValue call.storage 0)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt _ _)]
  have hc' : ((State.initial call).storage 0).toNat % 256 + x.toNat < 256 := by rw [hs]; exact hc
  have hlt : ¬ 255 < EvmRules.Evm.add (EvmRules.Evm.and ((State.initial call).storage 0) 255) x := by
    rw [BitVec.lt_def, toNat_add_low _ _ hc']
    show ¬ 255 < _
    omega
  have hw := BitVec.eq_of_toNat_eq ((slot_word_at _ x hx hc').trans
    (BitVec.toNat_ofNat _ _ |>.trans (Nat.mod_eq_of_lt (by
      have := ((State.initial call).storage 0).isLt
      have hy : ((State.initial call).storage 0).toNat / 256 % 256 ^^^ x.toNat < 2 ^ 8 :=
        Nat.xor_lt_two_pow (by omega) (by omega)
      omega))).symm)
  clear hs
  try comm_order at hlt hw
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, hgt])
  have hlb := low_byte_at _ x hc'
  try comm_order at hlb
  try comm_order
  rw [hlb]
  have hs : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    show (BitVec.ofNat 256 (slotValue call.storage 0)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt _ _)]
  rw [hs, SolidCore.Verify.C4.model_ok _ _ hx hc]
  simp only [observe, SolidCore.Verify.observe, Option.some.injEq, Observable.mk.injEq]
  have h0lt := slotValue_lt call.storage 0
  have hy : slotValue call.storage 0 / 256 % 256 ^^^ x.toNat < 2 ^ 8 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  refine ⟨trivial, ?_, rfl, ?_⟩
  · refine (read_store _ _).trans ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  · funext slot
    simp only [storageOf, update]
    split
    · rename_i e
      have h : slot % 2 ^ 256 = 0 := by simpa using congrArg BitVec.toNat e
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), BitVec.toNat_ofNat]
    · rename_i e
      have h : ¬ slot % 2 ^ 256 = 0 :=
        fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      simp only [State.initial, BitVec.toNat_ofNat]
      exact slotValue_mod_mod _ slot

set_option linter.unusedSimpArgs false in
/-- On a clean x where v + x overflows uint8, from any storage, stage0 reverts with Panic(0x11)
as Verify.C4.model does. -/
theorem mir_run_panic_of (o : Oracle) (call : Call) (x : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 33980010)
    (h4 : calldataWord call 4 = x) (hx : x.toNat < 256)
    (hc : ¬ slotValue call.storage 0 % 256 + x.toNat < 256) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 12).map (fun r => observe call r.2 r.1) =
      some (SolidCore.Verify.observe (slotValue call.storage)
        (SolidCore.Verify.C4.model [x.toNat] (slotValue call.storage))) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  have hgt := gt_255 x hx
  have hs : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    show (BitVec.ofNat 256 (slotValue call.storage 0)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (slotValue_lt _ _)]
  have hlt : 255 < EvmRules.Evm.add (EvmRules.Evm.and ((State.initial call).storage 0) 255) x := by
    rw [BitVec.lt_def]
    unfold EvmRules.Evm.add
    rw [BitVec.toNat_add, toNat_and_255, hs, Nat.mod_eq_of_lt (by omega)]
    show 255 < _
    omega
  clear hs
  try comm_order at hlt
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, hgt])
  rw [SolidCore.Verify.C4.model_panic _ _ hx hc]
  rfl

/-- SolarTV's lowered MIR semantics runs c4's first lowered MIR module on every call of add(x)
from any storage σ, under every oracle, to expectedAt σ x: the MIR reads slot 0 of σ as it is,
so σ need not write slot 0. -/
theorem mir_run_at (o : Oracle) (x : U256) (σ : List (Nat × Nat)) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0 (callAt addSelector [x] σ) =
      some (expectedAt σ x) := by
  by_cases hx : x.toNat < 256
  · by_cases hc : slotValue σ 0 % 256 + x.toNat < 256
    · exact mir_sem_of_run 12 (mir_run_ok_of o _ x rfl (size_callAt x σ) (word0' x σ) (word4 x σ)
        hx hc)
    · exact mir_sem_of_run 12 (mir_run_panic_of o _ x rfl (size_callAt x σ) (word0' x σ)
        (word4 x σ) hx hc)
  · refine mir_sem_of_run 12 ((mir_run_dirty_of o _ x rfl (size_callAt x σ) (word0' x σ)
      (word4 x σ) hx).trans ?_)
    simp only [expectedAt, Verify.C4.model_dirty x.toNat _ hx, Verify.observe]
    rfl

end Packed

/-! ## The source stage -/

/-- **The source stage of c4**: SolidCore to solar's first lowered MIR, which includes ABI
decoding and dispatch, on every call of add on any argument word, clean or dirty, from the
deployed storage, under every oracle. -/
theorem lowering (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.C4.scope := by
  intro call hscope obs hrun
  obtain ⟨x, rfl⟩ := scope_callAt hscope
  change Source.run Corpus.C4.fuel c (callAt addSelector [x] Verify.C4.deployed) = some obs at hrun
  rw [source_run_at hc x Verify.C4.deployed ⟨(0, 7 * 256), List.mem_singleton_self _, rfl⟩] at hrun
  cases hrun
  exact mir_run o x

/-- The source stage from any storage that writes slot 0, for any first lowered MIR module that
runs every such call of add as Verify.C4.model does (hmir). For solar's stage0, hmir is
mir_run_at (loweringAt). -/
theorem loweringAt_of_runs (o : SolarTV.Machine.Oracle) {m : SolarTV.MIR.Lowered.Module}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c)
    (hmir : ∀ (x : U256) (σ : List (Nat × Nat)), (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) →
      (SolarTV.MIR.Lowered.moduleSem o).run m (callAt addSelector [x] σ) = some (expectedAt σ x)) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c m Verify.C4.scopeAt := by
  intro call hscope obs hrun
  obtain ⟨x, σ, hσ, rfl⟩ := scopeAt_callAt hscope
  change Source.run Corpus.C4.fuel c (callAt addSelector [x] σ) = some obs at hrun
  rw [source_run_at hc x σ hσ] at hrun
  cases hrun
  exact hmir x σ hσ

/-- **The source stage of c4 from any storage**: SolidCore to solar's first lowered MIR, on every
call of add on any argument word, clean or dirty, with no value, from any storage that writes
slot 0, under every oracle: loweringAt_of_runs with stage0's run from any storage (mir_run_at). -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.C4.scopeAt :=
  loweringAt_of_runs o hc fun x σ _ => mir_run_at o x σ

/-! ## To the bytecode -/

/-- A stage into EthLib from a program that agrees with SolidCore (chain), when the bytecode
refines SolidCore on the scope: each observable of the program is SolidCore's, which is the
bytecode's. -/
theorem assembly_of_refines {fuel : Nat} {A : Sem} {p : A.Prog}
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray} {scope : Call → Prop}
    (href : Refines fuel c code scope) (chain : Stage (solidCore fuel) A c p scope) :
    Stage A ethLib p code scope := by
  intro call hs obs hrun
  obtain ⟨obs', h1, h2⟩ := href call hs
  have := chain call hs obs' h1
  rw [hrun] at this
  cases this
  exact h2

/-- **c4 through solar's stages.** Given the backend stage from solar's first lowered MIR to
an EVM IR program evm (solar-tv's certify.sh proves it on every call for each contract it
certifies), Verify.C4's specification holds of solar's bytecode Corpus.C4.code under EthLib, on
every call of add from the deployed storage: bytecode_of_stages with the source stage
(lowering), the backend, and the assembly stage from c4's refinement (Corpus.C4.refines_full). -/
theorem certified_of_backend (o : SolarTV.Machine.Oracle) {evmirSem : Sem} {evm : evmirSem.Prog}
    (backend : Stage (SolarTV.MIR.Lowered.moduleSem o) evmirSem SolarTV.Export.Main.stage0 evm
      Verify.C4.scope) :
    Satisfies ethLib Corpus.C4.code Verify.C4.scope Verify.C4.pre Verify.C4.post := by
  obtain ⟨c, hc, hs, hspec⟩ := Verify.C4.satisfies
  obtain ⟨c', s, hc', hs', href⟩ := Corpus.C4.refines_full
  rw [hc] at hc'
  cases hc'
  rw [hs] at hs'
  cases hs'
  have low := lowering o hc
  exact bytecode_of_stages hspec low backend (assembly_of_refines href (low.trans backend))

/-! ## To the bytecode from any storage

EthLib runs solar's bytecode Corpus.C4.code on every call of add from any storage σ to
expectedAt σ x (target_run_at), as stage0 does (mir_run_at): Evm.WideStorage's steps up to the
JUMPI on v + x, where the slot-0 word SLOAD read is named S, and then up to the RETURN or REVERT,
whose words tgt_slot_word and tgt_low_byte compute. Neither run needs σ to write slot 0; only
SolidCore's does (scopeAt), since it runs a call from σ written over the constructor's storage.

* mir_assemblyAt: lowered MIR to bytecode, stage0 to Corpus.C4.code, on scopeAt.
* assemblyAt_of_chain: the assembly stage for any program that agrees with SolidCore on
  scopeAt, such as the EVM IR a backend stage reaches from stage0.
* certifiedAt: Verify.C4's specification from any storage (postAt) holds of the bytecode through
  loweringAt and mir_assemblyAt. certifiedAt_of_backend: the same through a backend stage
  from stage0 to EVM IR (bytecode_of_stages).
* bytecode_satisfiesAll: the bytecode meets postAt on scopeAll, every call of add from every
  storage, slot 0 written or not, from target_run_at alone. -/

section TargetAt

open EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

/-- The low byte of a slot-0 word, as EthLib's AND leaves it. -/
theorem ofNat_and_255 (S : Nat) (hS : S < 2 ^ 256) :
    (BitVec.ofNat 256 S &&& 255#256) = BitVec.ofNat 256 (S % 256) := by
  apply BitVec.eq_of_toNat_eq
  have : (BitVec.ofNat 256 S &&& 255#256).toNat = S % 256 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS]
    exact Nat.and_two_pow_sub_one_eq_mod S 8
  rw [this, BitVec.toNat_ofNat]
  omega

/-- The word solar's bytecode writes to slot 0 from the slot-0 word S, under EthLib's operations,
when v + x fits in uint8: slot_word_at, since EthLib's BYTE and SHL are EvmRules'. -/
theorem tgt_slot_word (S : Nat) (x : U256) (hS : S < 2 ^ 256) (hx : x.toNat < 256)
    (hc : S % 256 + x.toNat < 256) :
    (115792089237316195423570985008687907853269984665640564039457584007913129574655#256 &&&
        (115792089237316195423570985008687907853269984665640564039457584007913129639680#256 &&&
            BitVec.ofNat 256 S ||| x + BitVec.ofNat 256 (S % 256)) |||
      bitwiseShl (8#256)
        (getByte (30#256)
            (115792089237316195423570985008687907853269984665640564039457584007913129639680#256 &&&
                BitVec.ofNat 256 S ||| x + BitVec.ofNat 256 (S % 256)) ^^^ x)) =
      BitVec.ofNat 256 (S / 65536 * 65536 + (S / 256 % 256 ^^^ x.toNat) * 256 + (S % 256 + x.toNat)) := by
  have hs : (BitVec.ofNat 256 S).toNat = S := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hS]
  have hc' : (BitVec.ofNat 256 S).toNat % 256 + x.toNat < 256 := by rw [hs]; exact hc
  have hlow : EvmRules.Evm.add (EvmRules.Evm.and (BitVec.ofNat 256 S) 255) x = x + BitVec.ofNat 256 (S % 256) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_low _ _ hc', BitVec.toNat_add, hs]
    simp only [BitVec.toNat_ofNat]
    omega
  have hb : ∀ v : U256, getByte (30#256) v = EvmRules.Evm.byte 30 v := fun v => rfl
  have hsh : ∀ v : U256, bitwiseShl (8#256) v = EvmRules.Evm.shl 8 v := fun v => rfl
  have e := slot_word_at (BitVec.ofNat 256 S) x hx hc'
  rw [hs, hlow] at e
  apply BitVec.eq_of_toNat_eq
  have hy : S / 256 % 256 ^^^ x.toNat < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hF : S / 65536 * 65536 + (S / 256 % 256 ^^^ x.toNat) * 256 + (S % 256 + x.toNat) < 2 ^ 256 := by
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF, ← e, hb, hsh]
  simp only [EvmRules.Evm.or, EvmRules.Evm.and, EvmRules.Evm.xor, BitVec.and_comm]
  rfl

/-- The low byte of that word, which the bytecode returns. -/
theorem tgt_low_byte (S : Nat) (x : U256) (hS : S < 2 ^ 256) (hc : S % 256 + x.toNat < 256) :
    255#256 &&& BitVec.ofNat 256 (S / 65536 * 65536 + (S / 256 % 256 ^^^ x.toNat) * 256 + (S % 256 + x.toNat)) =
      BitVec.ofNat 256 (S % 256 + x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hy : S / 256 % 256 ^^^ x.toNat < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hF : S / 65536 * 65536 + (S / 256 % 256 ^^^ x.toNat) * 256 + (S % 256 + x.toNat) < 2 ^ 256 := by
    omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF]
  rw [Nat.and_comm, show 255 % 2 ^ 256 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- EthLib runs solar's bytecode on add(x) from any storage, when x is clean and v + x fits in
uint8, to expectedAt σ x. -/
theorem target_run_ok (x : U256) (σ : List (Nat × Nat)) (hx : x.toNat < 256)
    (hc : slotValue σ 0 % 256 + x.toNat < 256) :
    Target.run Corpus.C4.code (callAt addSelector [x] σ) = some (expectedAt σ x) := by
  simp only [expectedAt, Verify.C4.model_ok _ _ hx hc, Verify.observe]
  refine run_of_postS_at Corpus.C4.code addSelector [x] σ _ rfl (fun h => by cases h) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [addSelector, Bytecode.C4.Main.addSelector] at hd
  repeat wide_one_at [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize,
    Bytecode.C4.Main.addSelector] [hd, hv] hfork hstat htgt
  -- Name the slot-0 word SLOAD read, which the steps above left as slotValue's fold over σ.
  obtain ⟨S, hS⟩ : ∃ S, slotValue σ 0 = S := ⟨_, rfl⟩
  have hSlt : S < 2 ^ 256 := hS ▸ slotValue_lt σ 0
  rw [hS] at hc
  simp only [slotValue, Nat.reduceMod, Nat.reducePow] at hS
  simp only [hS]
  have hlow := ofNat_and_255 S hSlt
  simp only [hlow]
  repeat wide_one_at [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize,
    Bytecode.C4.Main.addSelector] [hd, hv] hfork hstat htgt
  have hW := tgt_slot_word S x hSlt hx hc
  have hL := tgt_low_byte S x hSlt hc
  simp only [hW, hL]
  refine return_postS ?lt ?op ?gas ?succ ?out rfl ?store
  case lt => evm_code [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize]
  case op => evm_code [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize]
  case gas => wide_mem; omega
  case succ => rfl
  case out =>
    wide_mem
    rw [toList_wordBytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  case store =>
    intro slot
    simp only [htgt, getStorage_writeOf_of, getStorage_recordStorageRead, getStorage_preState_ofNat,
      storage_callAt, storageKey_eq_toBeBytes, BitVec.toNat_ofNat]
    simp only [Nat.reducePow, Nat.zero_mod, true_and]
    by_cases h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0
    · simp only [h, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow]
    · simp only [h, ↓reduceIte, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (slotValue_lt σ slot)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The same when v + x overflows uint8: a Panic(0x11) revert. -/
theorem target_run_panic (x : U256) (σ : List (Nat × Nat)) (hx : x.toNat < 256)
    (hc : ¬ slotValue σ 0 % 256 + x.toNat < 256) :
    Target.run Corpus.C4.code (callAt addSelector [x] σ) = some (expectedAt σ x) := by
  simp only [expectedAt, Verify.C4.model_panic _ _ hx hc, Verify.observe]
  refine run_of_postS_at Corpus.C4.code addSelector [x] σ _ rfl (fun _ _ => rfl) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [addSelector, Bytecode.C4.Main.addSelector] at hd
  repeat wide_one_at [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize,
    Bytecode.C4.Main.addSelector] [hd, hv] hfork hstat htgt
  -- Name the slot-0 word SLOAD read, which the steps above left as slotValue's fold over σ.
  obtain ⟨S, hS⟩ : ∃ S, slotValue σ 0 = S := ⟨_, rfl⟩
  have hSlt : S < 2 ^ 256 := hS ▸ slotValue_lt σ 0
  rw [hS] at hc
  simp only [slotValue, Nat.reduceMod, Nat.reducePow] at hS
  simp only [hS]
  have hlow := ofNat_and_255 S hSlt
  simp only [hlow]
  repeat wide_one_at [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize,
    Bytecode.C4.Main.addSelector] [hd, hv] hfork hstat htgt
  refine revert_postS (by decide) ?lt ?op ?gas ?succ ?out rfl
  case lt => evm_code [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize]
  case op => evm_code [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize]
  case gas => wide_mem; omega
  case succ => rfl
  case out =>
    wide_mem
    decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The same on a dirty word: a revert with empty data, before the bytecode reads storage. -/
theorem target_run_dirty (x : U256) (σ : List (Nat × Nat)) (hx : ¬ x.toNat < 256) :
    Target.run Corpus.C4.code (callAt addSelector [x] σ) = some (expectedAt σ x) := by
  simp only [expectedAt, Verify.C4.model_dirty _ _ hx, Verify.observe]
  refine run_of_postS_at Corpus.C4.code addSelector [x] σ _ rfl (fun _ _ => rfl) ?_
  intro msg hv hd hstat htgt
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [addSelector, Bytecode.C4.Main.addSelector] at hd
  repeat wide_one_at [Corpus.C4.code, Bytecode.C4.Main.runtimeNat, Bytecode.C4.Main.runtimeSize,
    Bytecode.C4.Main.addSelector] [hd, hv] hfork hstat htgt

/-- EthLib runs solar's bytecode on every call of add(x) from any storage σ to expectedAt σ x. -/
theorem target_run_at (x : U256) (σ : List (Nat × Nat)) :
    Target.run Corpus.C4.code (callAt addSelector [x] σ) = some (expectedAt σ x) := by
  by_cases hx : x.toNat < 256
  · by_cases hc : slotValue σ 0 % 256 + x.toNat < 256
    · exact target_run_ok x σ hx hc
    · exact target_run_panic x σ hx hc
  · exact target_run_dirty x σ hx

end TargetAt

/-- **The assembly-side stage of c4 from any storage**: solar's first lowered MIR to its
bytecode on EthLib, on every call of add with no value from any storage that writes slot 0,
under every oracle. -/
theorem mir_assemblyAt (o : SolarTV.Machine.Oracle) :
    Stage (SolarTV.MIR.Lowered.moduleSem o) ethLib SolarTV.Export.Main.stage0 Corpus.C4.code
      Verify.C4.scopeAt := by
  intro call hs obs hrun
  obtain ⟨x, σ, -, rfl⟩ := scopeAt_callAt hs
  rw [mir_run_at o x σ] at hrun
  cases hrun
  exact target_run_at x σ

/-- The assembly stage from any storage, for any program that agrees with SolidCore on scopeAt
(chain): each observable of the program is SolidCore's, which is the bytecode's. -/
theorem assemblyAt_of_chain {A : Sem} {p : A.Prog} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) (chain : Stage (solidCore Corpus.C4.fuel) A c p Verify.C4.scopeAt) :
    Stage A ethLib p Corpus.C4.code Verify.C4.scopeAt := by
  intro call hs obs hrun
  obtain ⟨x, σ, hσ, rfl⟩ := scopeAt_callAt hs
  have := chain _ hs _ (source_run_at hc x σ hσ)
  rw [hrun] at this
  cases this
  exact target_run_at x σ

/-- **c4 from any storage.** Verify.C4's specification from any storage that writes slot 0
(postAt) holds of solar's bytecode under EthLib, through the source stage from any storage
(loweringAt) and the assembly-side stage (mir_assemblyAt). -/
theorem certifiedAt (o : SolarTV.Machine.Oracle) :
    Satisfies ethLib Corpus.C4.code Verify.C4.scopeAt Verify.C4.pre Verify.C4.postAt := by
  obtain ⟨c, hc, hspec⟩ := Verify.C4.satisfiesAt
  exact SolidCore.Refinement.Satisfies.of_stage hspec ((loweringAt o hc).trans (mir_assemblyAt o))

/-- **c4 from any storage through solar's stages.** The same through a backend stage from
stage0 to an EVM IR program evm on scopeAt: bytecode_of_stages with loweringAt, the backend
and the assembly stage from evm (assemblyAt_of_chain). -/
theorem certifiedAt_of_backend (o : SolarTV.Machine.Oracle) {evmirSem : Sem} {evm : evmirSem.Prog}
    (backend : Stage (SolarTV.MIR.Lowered.moduleSem o) evmirSem SolarTV.Export.Main.stage0 evm
      Verify.C4.scopeAt) :
    Satisfies ethLib Corpus.C4.code Verify.C4.scopeAt Verify.C4.pre Verify.C4.postAt := by
  obtain ⟨c, hc, hspec⟩ := Verify.C4.satisfiesAt
  have low := loweringAt o hc
  exact bytecode_of_stages hspec low backend (assemblyAt_of_chain hc (low.trans backend))

/-! ### Every storage, on the bytecode -/

/-- The calls of add on any argument word, with no value, from every storage, whether or not
it writes slot 0. -/
def scopeAll : Call → Prop := fun call => ∃ σ, fullScope Corpus.C4.fns σ call

theorem scopeAll_callAt {call : Call} (h : scopeAll call) :
    ∃ (x : U256) (σ : List (Nat × Nat)), call = callAt addSelector [x] σ := by
  obtain ⟨σ, fn, hfn, args, hlen, hlt, rfl⟩ := h
  simp only [Corpus.C4.fns, List.mem_singleton] at hfn
  subst hfn
  match args, hlen with
  | [a], _ =>
    refine ⟨BitVec.ofNat 256 a, σ, ?_⟩
    have ha : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (hlt a (by simp))
    simp only [callAt, List.map_cons, List.map_nil, BitVec.toNat_ofNat, ha]

/-- The verification conditions of add from every storage: Verify.C4.vcsAt, whose proof does not
use the slot-0 write. -/
theorem vcsAll : ∀ call, scopeAll call → Verify.C4.pre call →
    Verify.vc Verify.C4.model (Verify.argWords 1) Verify.C4.postAt call := by
  rintro call ⟨σ, hs⟩ hp
  refine Verify.vcs_of_fullScope (fns := Corpus.C4.fns) (s := σ) (n := 1) (by simp [Corpus.C4.fns])
    ?_ call hs hp
  intro fn hfn call args hcall hw hlen hargs hinit _
  subst hcall
  match args, hlen with
  | [x], _ =>
    have hx : x < 2 ^ 256 := hargs x (by simp)
    have hs0 := slotValue_lt σ 0
    rw [Verify.wp_eq]
    simp only [Verify.C4.postAt, hw, List.getD_cons_zero]
    by_cases h1 : x < 256
    · by_cases h2 : slotValue σ 0 % 256 + x < 256
      · rw [Verify.C4.model_ok x _ h1 h2]
        simp only [Nat.reducePow, h1, h2, ↓reduceIte, true_and]
        refine ⟨fun slot => ?_, trivial⟩
        split
        · exact Nat.mod_eq_of_lt (by
            have := Nat.xor_lt_two_pow (n := 8) (x := slotValue σ 0 / 256 % 256) (y := x)
              (by omega) (by omega)
            omega)
        · rfl
      · rw [Verify.C4.model_panic x _ h1 h2]
        simp [h1, h2]
    · rw [Verify.C4.model_dirty x _ h1]
      simp [h1]

/-- **solar's bytecode for c4 meets postAt from every storage**, slot 0 written or not, under
EthLib: target_run_at runs it to the model's outcome from the call's storage, which vcsAll
shows meets postAt. SolidCore needs slot 0 written (scopeAt), the bytecode does not. -/
theorem bytecode_satisfiesAll :
    Satisfies ethLib Corpus.C4.code scopeAll Verify.C4.pre Verify.C4.postAt := by
  intro call hs hp
  have h := vcsAll call hs hp
  obtain ⟨x, σ, rfl⟩ := scopeAll_callAt hs
  refine ⟨_, target_run_at x σ, ?_⟩
  have hw : Verify.argWords 1 (callAt addSelector [x] σ) = [x.toNat] := by
    obtain ⟨_, fn, hfn, args, hlen, hlt, hcall⟩ := hs
    have := Verify.argWords_calldata addSelector [x.toNat] (by simp [x.isLt]) 0 σ
    simpa [callAt] using this
  have hi : Verify.initStorage (callAt addSelector [x] σ) = slotValue σ := rfl
  simp only [Verify.vc, Verify.wp_eq, hw, hi] at h
  show Verify.C4.postAt _ (Verify.observe (slotValue σ) (Verify.C4.model [x.toNat] (slotValue σ)))
  revert h
  rcases Verify.C4.model [x.toNat] (slotValue σ) with e | ⟨out, s'⟩ <;> exact id

/-- info: 'SolidCore.Refinement.Solar.C4.mir_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mir_run

/-- info: 'SolidCore.Refinement.Solar.C4.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.C4.loweringAt_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt_of_runs

/-- info: 'SolidCore.Refinement.Solar.C4.slot_word_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slot_word_at

/-- info: 'SolidCore.Refinement.Solar.C4.mir_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mir_run_at

/-- info: 'SolidCore.Refinement.Solar.C4.loweringAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt

/-- info: 'SolidCore.Refinement.Solar.C4.certified_of_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_of_backend

/-- info: 'SolidCore.Refinement.Solar.C4.target_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_run_at

/-- info: 'SolidCore.Refinement.Solar.C4.mir_assemblyAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mir_assemblyAt

/-- info: 'SolidCore.Refinement.Solar.C4.certifiedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedAt

/-- info: 'SolidCore.Refinement.Solar.C4.certifiedAt_of_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedAt_of_backend

/-- info: 'SolidCore.Refinement.Solar.C4.bytecode_satisfiesAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytecode_satisfiesAll

end SolidCore.Refinement.Solar.C4
