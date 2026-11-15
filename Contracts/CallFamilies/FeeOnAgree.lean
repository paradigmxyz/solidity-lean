import Contracts.CallFamilies.FeeOnMir
import Contracts.CallFamilies.SyncAgree

/-!
# `feeOn` in solar's MIR under the oracle hypothesis

`mir_feeOn_agree`: under `CallsAgree o V`, when SolidCore's `feeOn()` asks `V` the call `FeeOnAsk`
describes (a `STATICCALL` of the factory in slot 0 with `feeTo()`'s selector) and `V` answers `a`,
solar's stage0 shows `obsOf σ a`: the callee's revert data, an empty revert for short return data
or a dirty address, else `true` with slot 3 set to 1 for a nonzero `feeTo`, or `false`.
-/

namespace SolidCore.Refinement.CallFamilies.FeeOn

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement
open SolidCore.Refinement.CallFamilies.Sync (retWord bytes_write bytes_expand lt_word callFlag_cases)
open EvmCompiler.Simulation
open SolidCore.Solidity.Source (addressToWord u256ToWord byteArrayToBytes)

set_option linter.deprecated false

/-- The 32 bytes of a returned word. -/
def wordBytes (x : BitVec 256) : List Nat := (List.range 32).map fun i => (Memory.byte x i).toNat

/-- What `feeOn()` shows when the factory answers `a`. -/
def obsOf (σ : List (Nat × Nat)) (a : CallResponse) : Observable :=
  if a.success then
    if a.returnData.size < 32 then ⟨false, [], [], slotValue σ⟩
    else if 2 ^ 160 ≤ (retWord a).toNat then ⟨false, [], [], slotValue σ⟩
    else if retWord a = 0 then
      ⟨true, wordBytes 0, [], fun slot => ((State.initial (feeOnCall σ)).storage (BitVec.ofNat 256 slot)).toNat⟩
    else ⟨true, wordBytes 1, [], fun slot =>
      (update (State.initial (feeOnCall σ)).storage 3 1 (BitVec.ofNat 256 slot)).toNat⟩
  else ⟨false, (List.range a.returnData.size).map (fun j => (a.returnData.get! j).toNat), [],
    slotValue σ⟩

/-- The call SolidCore's `feeOn()` asks `V`, with its answer. -/
structure FeeOnAsk (σ : List (Nat × Nat)) (V : World) (world : SolidCore.Solidity.Shared.OpenWorld)
    (request : CallRequest) (a : CallResponse) : Prop where
  ans : V.ans [] (.external world (.call request)) = some a
  kind : request.kind = .staticcall
  callee : addressToWord request.codeAddress = slotValue σ 0 % 2 ^ 160
  value : u256ToWord request.transferValue = 0
  input : byteArrayToBytes request.calldata = input.map BitVec.toNat
  storage : ∀ slot < 2 ^ 256, storageIn world slot = slotValue σ slot % 2 ^ 256
  transient : ∀ slot < 2 ^ 256, transientIn world slot = 0
  codes : ∀ x < 2 ^ 160, (codeIn world x).isEmpty =
    (SolidCore.Solidity.Shared.Account.codeAt (V.codes.getD []) x).isEmpty
  size : a.returnData.size < 2 ^ 256

theorem answer (o : Oracle) (V : World) (σ : List (Nat × Nat))
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : FeeOnAsk σ V world request a) :
    ((callFlag o (W o σ) = 1) ↔ a.success = true) ∧
      (returndataSize o (W o σ)).toNat = a.returnData.size ∧
      ∀ j < a.returnData.size, (returndataByte o (W o σ) j).toNat = (a.returnData.get! j).toNat := by
  have hcalls : machineCalls (W o σ) =
      sourceCalls ([] ++ [⟨.external world (.call request), a⟩]) := by
    simp only [W, machineCalls, sourceCalls, List.nil_append, hs.kind, hs.callee, hs.value, hs.input,
      machineKind, List.getD]
    simp
  have hstore : ∀ slot < 2 ^ 256,
      ((State.initial (feeOnCall σ)).storage (BitVec.ofNat 256 slot)).toNat = storageIn world slot ∧
        ((fun _ => (0 : BitVec 256)) (BitVec.ofNat 256 slot)).toNat = transientIn world slot := by
    intro slot hslot
    refine ⟨?_, ?_⟩
    · rw [hs.storage slot hslot]
      simp only [State.initial, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hslot]
      rfl
    · rw [hs.transient slot hslot]; rfl
  have hcodes : CodesAgree o (W o σ).dropLast (codeIn world) := by
    intro x hx
    rw [hs.codes x hx]
    exact agree.codes [.read "gas"] rfl x hx
  obtain ⟨hflag, -, hrest⟩ := agree.calls [] world request a hs.ans (W o σ) .staticcall _ _ _ _
    rfl hcalls hstore hcodes
  obtain ⟨hsz, hby, -⟩ := hrest [] rfl
  simp only [List.append_nil] at hsz hby
  refine ⟨hflag, ?_, fun j hj => hby j hj (Nat.lt_trans hj hs.size)⟩
  rw [hsz, Nat.mod_eq_of_lt hs.size]

theorem gt_mask (v : BitVec 256) : EvmRules.Evm.gt v mask = if 2 ^ 160 ≤ v.toNat then 1 else 0 := by
  change (bif mask.ult v then (1 : BitVec 256) else 0) = _
  rw [cond_eq_if]
  have hm : mask.toNat = 2 ^ 160 - 1 := rfl
  have hiff : (mask.ult v = true) ↔ 2 ^ 160 ≤ v.toNat := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  by_cases h : 2 ^ 160 ≤ v.toNat
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem ne_zero (v : BitVec 256) : EvmRules.Evm.ne v 0 = if v = 0 then 0 else 1 := by
  unfold EvmRules.Evm.ne
  by_cases h : v = 0 <;> simp [h]

theorem read_store (m : Mem) (x : BitVec 256) :
    ((m.store 0 x).expand 0 32).read 0 32 = (List.range 32).map fun i => Memory.byte x i := by
  unfold Mem.read
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [bytes_expand]
  unfold Mem.store
  rw [bytes_expand]
  simp [hi]

/-- **feeOn's MIR under the oracle hypothesis.** -/
theorem mir_feeOn_agree (o : Oracle) (V : World) (σ : List (Nat × Nat))
    (world : SolidCore.Solidity.Shared.OpenWorld) (request : CallRequest) (a : CallResponse)
    (agree : CallsAgree o V) (hs : FeeOnAsk σ V world request a) :
    (moduleSem o).run SolarTV.Export.Calls.stage0 (feeOnCall σ) = some (obsOf σ a) := by
  obtain ⟨hflag, hsize, hbytes⟩ := answer o V σ world request a agree hs
  rw [sem_feeOn]
  congr 1
  unfold feeOnEnd obsOf
  by_cases hsucc : a.success = true
  · have hf : callFlag o (W o σ) ≠ 0 := by
      intro h; have := hflag.mpr hsucc; rw [h] at this; exact absurd this (by decide)
    rw [if_neg hf, if_pos hsucc, lt_word, hsize]
    by_cases hlt : a.returnData.size < 32
    · have : ((if a.returnData.size < (32 : BitVec 256).toNat then (1 : BitVec 256) else 0) ≠ 0) := by
        simp [hlt]
      rw [if_pos this, if_pos hlt]
      rfl
    · have : ¬ ((if a.returnData.size < (32 : BitVec 256).toNat then (1 : BitVec 256) else 0) ≠ 0) := by
        simp [hlt]
      rw [if_neg this, if_neg hlt]
      have hload : ret o σ = retWord a := by
        unfold ret Mem.load Mem.read retWord
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        have hmin : min 32 (returndataSize o (W o σ)).toNat = 32 := by rw [hsize]; omega
        rw [M4, bytes_write, hmin]
        simp only [Nat.zero_le, Nat.zero_add, hi, and_self, if_true, Nat.sub_zero]
        apply BitVec.eq_of_toNat_eq
        rw [hbytes i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
      rw [hload, gt_mask, ne_zero]
      by_cases hd : 2 ^ 160 ≤ (retWord a).toNat
      · rw [if_pos hd, if_pos (by decide), if_pos hd]
        rfl
      · rw [if_neg hd, if_neg (by decide), if_neg hd]
        by_cases hz : retWord a = 0
        · rw [if_pos hz, if_pos rfl, if_pos hz]
          simp only [halt, observe]
          rfl
        · rw [if_neg hz, if_neg (by decide), if_neg hz]
          simp only [halt, observe]
          rfl
  · have hf : callFlag o (W o σ) = 0 := by
      rcases callFlag_cases o (W o σ) with h | h
      · exact h
      · exact absurd (hflag.mp h) hsucc
    rw [if_pos hf, if_neg hsucc]
    simp only [halt, if_true, observe]
    congr 1
    rw [hsize]
    unfold Mem.read
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, bytes_expand, bytes_write, Nat.zero_le, Nat.zero_add]
    simp [hi]
    exact hbytes i hi

/-- info: 'SolidCore.Refinement.CallFamilies.FeeOn.mir_feeOn_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mir_feeOn_agree

end SolidCore.Refinement.CallFamilies.FeeOn
