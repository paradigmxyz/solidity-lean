import SolidCore.Refinement.Solar.Counter.Value
import SolidCore.Refinement.Dyn.Source

/-!
# counter on every call: get, malformed call data and unknown selectors

Counter has no fallback and no receive function, so SolidCore and solar's code reject every call
that names no function or whose arguments do not decode. This file proves each class of call
through the source stage, from any storage:

* get(), with no value: success returning the word in slot 0, the storage kept
  (source_run_get, mir_run_get).
* call data shorter than 4 bytes, with any bytes and any value: rejected (source_run_short).
* any 4-byte selector other than inc's and get's, followed by any bytes, with any value:
  rejected (source_run_unknown).
* inc's selector followed by fewer than 32 bytes, with any value: rejected
  (source_run_shortArgs).
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Verify

/-- Source.run of any call, once the constructor's result is known: the constructor runs with no
value whatever the call's, so it is the deployed state, and the ABI dispatcher of the core
contract runs on the call's bytes with its value. -/
theorem run_eq_any {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : DeployedAt fuel c d s) (call : Call) :
    Source.run fuel c call =
      Option.map (Source.observe call)
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core
          { ctxOf c with value := call.callvalue }
          { d with storage :=
            call.storage.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress callerAddress call.callvalue (call.calldata.data.toList.map (·.toNat))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  have hc' : TypeCheck.CheckedContract.constructWithContext? fuel c
      { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
      State.empty selfAddress 0 [] = some (CallResult.returned d vs) := hc
  simp only [Source.run, Source.result?]
  rw [hc']
  rfl

/-- The deployed state of SolidCore's checked Counter, with its core. -/
theorem deployed_counter {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    c.core = coreLit ∧ ∃ d, DeployedAt fuel c d [] := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  exact ⟨hk, d, deployedAt_of_deployed hd⟩

/-- SolidCore rejects every call whose call data is shorter than a selector, with any bytes and
any value, from any storage: no selector is read, and Counter has no receive or fallback
function. -/
theorem source_run_short {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (call : Call)
    (hsize : call.calldata.size < 4) :
    Source.run fuel c call = some (Abi.rejected call.storage) := by
  obtain ⟨hcore, d, hd⟩ := deployed_counter hc
  rw [run_eq_any hd, hcore]
  have hsel : ABI.readSelector? (call.calldata.data.toList.map (·.toNat)) = none := by
    simp only [ABI.readSelector?, ABI.readBytes?, ABI.selectorBytes, List.drop_zero,
      List.length_map, Array.length_toList]
    have h4 : call.calldata.data.size < 4 := hsize
    rw [ite_eq_right_iff.mpr (by omega)]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, hsel]
  simp only [ABI.Contract.callReceiveOrFallbackAtFromWithContext?,
    ABI.Contract.callFallbackAtFromWithContext?, ABI.Contract.findReceive?,
    ABI.Contract.findFallback?, Contract.findFunctionByName?, coreLit]
  split <;> simp [ABI.Contract.missingFallbackCall?, ABI.Contract.revertedEmptyCall?,
    ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, Source.observe, Abi.rejected]


open SolidCore.Refinement.Dyn in
/-- SolidCore rejects every call of a selector other than inc's and get's, followed by any
bytes, and every call of inc whose argument is shorter than a word, with any value, from any
storage: Counter has no fallback, and inc's argument does not decode. -/
theorem source_run_selector {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (s : Nat)
    (hs : s < 2 ^ 32) (data : ByteArray)
    (h : (s ≠ incSelector ∧ s ≠ getSelector) ∨ (s = incSelector ∧ data.size < 32)) (v : Nat)
    (σ : List (Nat × Nat)) :
    Source.run fuel c { calldata := Evm.selectorOf s ++ data, callvalue := v, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨hcore, d, hd⟩ := deployed_counter hc
  rw [run_eq_any hd, hcore]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, bytes_callOn,
    readSelector_append _ hs]
  have hm : s % 2 ^ 256 = s := Nat.mod_eq_of_lt (by omega)
  rcases h with ⟨h1, h2⟩ | ⟨rfl, hlt⟩
  · have hw1 : wordEq 2166751455 s = false := by
      simp only [wordEq, Shared.norm, Shared.wordModulus, beq_eq_false_iff_ne, ne_eq]
      simp only [incSelector, getSelector] at h1 h2
      rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl, hm]
      exact fun e => h1 (by rw [← e]; exact Nat.mod_eq_of_lt (by decide))
    have hw2 : wordEq 1833756220 s = false := by
      simp only [wordEq, Shared.norm, Shared.wordModulus, beq_eq_false_iff_ne, ne_eq]
      simp only [incSelector, getSelector] at h1 h2
      rw [show EvmYul.UInt256.size = 2 ^ 256 from rfl, hm]
      exact fun e => h2 (by rw [← e]; exact Nat.mod_eq_of_lt (by decide))
    simp only [Contract.findFunctionBySelector?, coreLit, List.find?, hw1, hw2]
    simp [ABI.Contract.callFallbackAtFromWithContext?, ABI.Contract.findFallback?,
      Contract.findFunctionByName?, ABI.Contract.missingFallbackCall?,
      ABI.Contract.revertedEmptyCall?, ABI.Contract.revertedCall?,
      ABI.Contract.encodeRevertData?, Source.observe, Abi.rejected]
  · have hw1 : wordEq 2166751455 incSelector = true := by decide
    simp only [Contract.findFunctionBySelector?, coreLit, List.find?, hw1]
    rw [show ((natToBytes 4 incSelector).map (·.toNat) ++ srcBytes data).drop ABI.selectorBytes =
        srcBytes data by simp [ABI.selectorBytes, natToBytes_length],
      decode_malformed _ [.word (.uint 256)] (by decide) data
        (Or.inl (by simpa [headWords, DParam.headWords] using hlt))]
    simp [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, Source.observe, Abi.rejected]


/-! ## get() from any storage -/

/-- What a call of get() from the storage σ shows: success returning the word in slot 0, with
no logs and σ kept. -/
def getAt (σ : List (Nat × Nat)) : Observable :=
  { success := true, output := Verify.word (slotValue σ 0), logs := [], storage := slotValue σ }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs get() with no value from any storage σ to getAt σ. -/
theorem source_run_get {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) :
    Source.run fuel c (callAt getSelector [] σ) = some (getAt σ) := by
  obtain ⟨hcore, d, hd⟩ := deployed_counter hc
  rw [run_eq_at hd]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  simp only [hcore, List.map_nil]
  wide_symex [coreLit, fuel, ctxOf, hcore, getSelector, get?_insert]
  all_goals
    have hlt := slotValue_lt σ 0
    have hlt' : slotValue σ 0 <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := hlt
    have hx := hget 0
    simp only [Nat.zero_mod] at hx
  case h_1 =>
    rename_i _ w heq
    simp only [heq, Option.getD_some] at hx
    subst hx
    simp only [Nat.mod_eq_of_lt hlt']
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?, getAt, Verify.word]
    funext slot
    have hs := hget slot
    simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size]
    simp only [Nat.reducePow] at hs
    rw [← hs]
    cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl
  case h_2 =>
    rename_i _ heq
    simp only [heq, Option.getD_none] at hx
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?, getAt, Verify.word,
      ← hx]
    funext slot
    have hs := hget slot
    simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size]
    simp only [Nat.reducePow] at hs
    rw [← hs]
    cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl


section CallsMIR

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

/-- SolarTV's lowered MIR runs stage0 on every call of get's selector with no value, whatever
the rest of its call data, from any storage, to getAt: the storage read of slot 0 and its
return. -/
theorem mir_run_get_of (o : Oracle) (call : Call) (hv : call.callvalue = 0)
    (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 1833756220) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (getAt call.storage) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  have hX : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    simp only [State.initial, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (slotValue_lt _ _)
  simp only [Machine.observe, getAt, Option.some.injEq, Observable.mk.injEq, true_and]
  refine ⟨?_, rfl, ?_⟩
  · rw [SolidCore.Refinement.Solar.W1.read_store_mir, hX]
    rfl
  · funext slot
    simp [storageOf, State.initial]
    exact slotValue_mod_mod call.storage slot

/-- SolarTV's lowered MIR rejects every call with no value whose selector word is neither
inc's nor get's, and every call of inc's selector shorter than 36 bytes, from any storage. -/
theorem mir_run_reject_of (o : Oracle) (call : Call) (hv : call.callvalue = 0)
    (h : (EvmRules.Evm.shr 224 (calldataWord call 0) ≠ 1833756220 ∧
      EvmRules.Evm.shr 224 (calldataWord call 0) ≠ 2166751455) ∨
      (EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455 ∧ call.calldata.size < 36)) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (Abi.rejected call.storage) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  rcases h with ⟨h1, h2⟩ | ⟨h0, hs⟩
  · have h1' := Ne.symm h1
    have h2' := Ne.symm h2
    repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
    simp [Machine.observe, Abi.rejected, Mem.read]
  · have hlt : BitVec.ofNat 256 call.calldata.size < 36 := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hs
    repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
    simp [Machine.observe, Abi.rejected, Mem.read]

end CallsMIR


/-! ## The selector word -/

section Selector

open SolarTV SolarTV.Machine EthLib.Execution.Evm SolidCore.Refinement.Evm

/-- The selector the code reads: the first 4 bytes of the call data, zero past its end. -/
def selWord (call : Call) : Nat := bytesToNat (bufferRead call.calldata 0 4)

/-- SHR 224 of the first call data word is the selector word. -/
theorem shr_word0 (call : Call) :
    EvmRules.Evm.shr 224 (calldataWord call 0) = BitVec.ofNat 256 (selWord call) := by
  rw [SolidCore.Refinement.Solar.W1.calldataWord_eq]
  have h := bitwiseShr_loadWord_zero call.calldata 4 (by decide) (by decide)
  rw [show BitVec.ofNat 256 (8 * (32 - 4)) = 224#256 from rfl] at h
  simpa [EvmRules.Evm.shr, bitwiseShr, selWord] using h

/-- The selector word of a selector followed by any bytes is the selector. -/
theorem selWord_append (s : Nat) (hs : s < 2 ^ 32) (data : ByteArray) (v : Nat)
    (σ : List (Nat × Nat)) :
    selWord { calldata := selectorOf s ++ data, callvalue := v, storage := σ } = s := by
  simp only [selWord]
  rw [bufferRead_append_of_le _ _ (by simp [size_selectorOf]), ← size_selectorOf s,
    bufferRead_zero_size, bytesToNat_selectorOf s hs]

/-- The selector word of call data shorter than 4 bytes ends in a zero byte, so it is neither
inc's selector nor get's. -/
theorem selWord_short (call : Call) (h : call.calldata.size < 4) :
    selWord call ≠ getSelector ∧ selWord call ≠ incSelector := by
  have hb3 : byteAt call.calldata 3 = 0 := by
    unfold byteAt
    rw [dite_eq_right_iff.mpr fun h' => absurd h' (by omega)]
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [selWord, bufferRead, hr, List.map, Nat.zero_add, hb3, bytesToNat, List.foldl,
    UInt8.toNat_zero, Nat.add_zero, getSelector, incSelector]
  omega

/-- The selector word is below 2 ^ 32. -/
theorem selWord_lt (call : Call) : selWord call < 2 ^ 32 := by
  have h := bytesToNat_lt (bufferRead call.calldata 0 4)
  simpa [bufferRead_length, selWord] using h

/-- SHR 224 of the first call data word is a selector exactly when the selector word is. -/
theorem shr_word0_eq (call : Call) (s : Nat) (hs : s < 2 ^ 32) :
    EvmRules.Evm.shr 224 (calldataWord call 0) = BitVec.ofNat 256 s ↔ selWord call = s := by
  rw [shr_word0]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    have h1 := selWord_lt call
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · intro e
    rw [e]

end Selector

open SolidCore.Refinement.Dyn in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore runs get's selector followed by any bytes, with no value, from any storage σ, to
getAt σ: get takes no arguments, so the bytes after the selector are not read. -/
theorem source_run_get_tail {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (data : ByteArray) (σ : List (Nat × Nat)) :
    Source.run fuel c
        { calldata := Evm.selectorOf getSelector ++ data, callvalue := 0, storage := σ } =
      some (getAt σ) := by
  obtain ⟨hcore, d, hd⟩ := deployed_counter hc
  rw [run_eq_any hd, hcore]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, bytes_callOn,
    readSelector_append _ (by decide : getSelector < 2 ^ 32)]
  have hw1 : wordEq 2166751455 getSelector = false := by decide
  have hw2 : wordEq 1833756220 getSelector = true := by decide
  simp only [Contract.findFunctionBySelector?, coreLit, List.find?, hw1, hw2]
  have hev := hd.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd.getElem?_eq_none (by simp)
  have hget := getD_storage h0 σ
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m at hget
  generalize srcBytes data = rest
  wide_symex [coreLit, fuel, ctxOf, hcore, getSelector, get?_insert]
  all_goals
    have hlt := slotValue_lt σ 0
    have hlt' : slotValue σ 0 <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := hlt
    have hx := hget 0
    simp only [Nat.zero_mod] at hx
  case h_1 =>
    rename_i _ w heq
    simp only [heq, Option.getD_some] at hx
    subst hx
    simp only [Nat.mod_eq_of_lt hlt']
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?, getAt, Verify.word]
    funext slot
    have hs := hget slot
    simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size]
    simp only [Nat.reducePow] at hs
    rw [← hs]
    cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl
  case h_2 =>
    rename_i _ heq
    simp only [heq, Option.getD_none] at hx
    simp [Source.observe, State.logEntries, State.loadSlot, StorageMap.lookup?, getAt, Verify.word,
      ← hx]
    funext slot
    have hs := hget slot
    simp only [Shared.norm, Shared.wordModulus, EvmYul.UInt256.size]
    simp only [Nat.reducePow] at hs
    rw [← hs]
    cases m[slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936]? <;> rfl

end SolidCore.Refinement.Solar.Counter
