import SolidCore.Refinement.Solar.Counter.Calls
import SolidCore.Refinement.Solar.Counter.AssemblyAt

/-!
# The counter on every call

expectedEvery is what Counter does on any call, as solar's code reads it: a call with value is
rejected (neither function is payable); otherwise the selector word (the first 4 bytes of the
call data, zero past its end) picks get, which returns slot 0, or inc, which needs 36 bytes and
adds the word at byte 4 to slot 0 or panics on overflow; anything else is rejected, since
Counter has no fallback and no receive function.

certifiedEvery states that solar's bytecode for Counter shows expectedEvery on every call of
scopeEvery, from any storage, under EthLib, through every stage of solar's pipeline:
scopeEvery is every call with a value below 2 ^ 256 whose call data is inc's ABI encoding of a
word, get's selector, shorter than a selector, or a selector followed by any bytes that is
neither inc's nor get's or is inc's with fewer than 32 bytes after it.

* source: source_run_every, from SpecAt.lean (inc), Value.lean (any value) and Calls.lean
  (get, short call data, unknown selectors, short arguments); mir_run_every, the lowered MIR's
  run of the same calls; loweringEvery is the stage.
* backend: SolarTV.Milestone.Counter.counter_mir_to_evmir, which holds on every call.
* assembly: assemblyEvery is the generic theorem, Assemble.stage_of_check_all at check_ok
  (stageAll), which holds on every call, with any value, call data and storage.

Not covered: call data that encodes inc or get but carries extra bytes after the ABI encoding.
The bytecode and MIR accept such calls as solc does; SolidCore's run of them is not proved
here.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Wide
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Evm SolidCore.Solidity SolidCore.Verify

/-- What Counter does on any call, from the call's storage. -/
def expectedEvery (call : Call) : Observable :=
  if call.callvalue ≠ 0 then Abi.rejected call.storage
  else if selWord call = getSelector then getAt call.storage
  else if selWord call = incSelector ∧ 36 ≤ call.calldata.size then
    expectedAt call.storage (EthLib.Execution.Evm.loadWord call.calldata 4 32)
  else Abi.rejected call.storage

/-- Every call with a value below 2 ^ 256, from any storage, whose call data is inc's ABI
encoding of a word, get's selector, shorter than a selector, or a selector followed by any
bytes that names no function or gives inc fewer than 32 bytes. -/
def scopeEvery : Call → Prop := fun call => call.callvalue < 2 ^ 256 ∧
  ((∃ d : U256, call.calldata = (callOf incSelector [d]).calldata) ∨
    call.calldata = (callOf getSelector []).calldata ∨
    call.calldata.size < 4 ∨
    ∃ (s : Nat) (data : ByteArray), s < 2 ^ 32 ∧ call.calldata = selectorOf s ++ data ∧
      ((s ≠ incSelector ∧ s ≠ getSelector) ∨ (s = incSelector ∧ data.size < 32)))

/-- The call shows expectedEvery. -/
def postEvery (call : Call) (obs : Observable) : Prop := obs = expectedEvery call

/-! ## The classes of calls -/

theorem calldata_inc (d : U256) :
    (callOf incSelector [d]).calldata = selectorOf incSelector ++ wordsBytes [d] := by
  rw [calldata_callOf]
  rfl

theorem calldata_get : (callOf getSelector []).calldata = selectorOf getSelector ++ .empty := by
  have := calldata_eq_cdOf getSelector [] (by simp)
  simpa [callOf, cdOf, wordsBytes] using this

theorem call_eta (call : Call) :
    call = { calldata := call.calldata, callvalue := call.callvalue, storage := call.storage } :=
  rfl

theorem expectedEvery_value (call : Call) (hv : call.callvalue ≠ 0) :
    expectedEvery call = Abi.rejected call.storage := by
  simp [expectedEvery, hv]

theorem expectedEvery_inc (d : U256) (σ : List (Nat × Nat)) :
    expectedEvery { callOf incSelector [d] with storage := σ } = expectedAt σ d := by
  have hs : selWord { callOf incSelector [d] with storage := σ } = incSelector := by
    have := selWord_append incSelector (by decide) (wordsBytes [d]) 0 σ
    rw [← calldata_inc] at this
    exact this
  have hsize := size_callOf d
  have hw : EthLib.Execution.Evm.loadWord (callOf incSelector [d]).calldata 4 32 = d := by
    have := word4 d
    rwa [SolidCore.Refinement.Solar.W1.calldataWord_eq] at this
  simp only [expectedEvery, hs]
  simp [callOf, incSelector, getSelector] at hsize hw ⊢
  simp [hsize, hw]

theorem expectedEvery_get (σ : List (Nat × Nat)) :
    expectedEvery (callAt getSelector [] σ) = getAt σ := by
  have hs : selWord (callAt getSelector [] σ) = getSelector := by
    have := selWord_append getSelector (by decide) .empty 0 σ
    rw [← calldata_get] at this
    exact this
  simp only [expectedEvery, hs, show (callAt getSelector [] σ).callvalue = 0 from rfl,
    show (callAt getSelector [] σ).storage = σ from rfl]
  rfl

theorem expectedEvery_short (call : Call) (h : call.calldata.size < 4) (hv : call.callvalue = 0) :
    expectedEvery call = Abi.rejected call.storage := by
  obtain ⟨h1, h2⟩ := selWord_short call h
  simp [expectedEvery, hv, h1, h2]

theorem expectedEvery_selector (s : Nat) (hs : s < 2 ^ 32) (data : ByteArray)
    (h : (s ≠ incSelector ∧ s ≠ getSelector) ∨ (s = incSelector ∧ data.size < 32))
    (σ : List (Nat × Nat)) :
    expectedEvery { calldata := selectorOf s ++ data, callvalue := 0, storage := σ } =
      Abi.rejected σ := by
  have hw := selWord_append s hs data 0 σ
  rcases h with ⟨h1, h2⟩ | ⟨rfl, hlt⟩
  · simp [expectedEvery, hw, h1, h2]
  · have hsize : (selectorOf incSelector ++ data).size = 4 + data.size := by
      simp [ByteArray.size_append, size_selectorOf]
    simp only [expectedEvery, hw, hsize]
    simp [incSelector, getSelector]
    omega


/-! ## Every stage -/

/-- **SolidCore on every call of the scope**: it shows expectedEvery. -/
theorem source_run_every {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (call : Call)
    (h : scopeEvery call) : Source.run fuel c call = some (expectedEvery call) := by
  rcases call with ⟨cd, v, σ⟩
  obtain ⟨hv, hcl⟩ := h
  dsimp only at hv hcl
  rcases hcl with ⟨d, rfl⟩ | rfl | hshort | ⟨s, data, hs, rfl, hsel⟩
  · by_cases h0 : v = 0
    · subst h0
      have := expectedEvery_inc d σ
      exact (source_run_at hc d σ).trans (congrArg some this.symm)
    · rw [expectedEvery_value _ h0]
      exact source_run_value hc incSelector [d] (Or.inl ⟨rfl, rfl⟩) v h0 hv σ
  · by_cases h0 : v = 0
    · subst h0
      have := expectedEvery_get σ
      exact (source_run_get hc σ).trans (congrArg some this.symm)
    · rw [expectedEvery_value _ h0]
      exact source_run_value hc getSelector [] (Or.inr ⟨rfl, rfl⟩) v h0 hv σ
  · by_cases h0 : v = 0
    · subst h0
      rw [expectedEvery_short _ hshort rfl]
      exact source_run_short hc _ hshort
    · rw [expectedEvery_value _ h0]
      exact source_run_short hc _ hshort
  · by_cases h0 : v = 0
    · subst h0
      rw [expectedEvery_selector s hs data hsel σ]
      exact source_run_selector hc s hs data hsel 0 σ
    · rw [expectedEvery_value _ h0]
      exact source_run_selector hc s hs data hsel v σ

/-- The specification on every call of the scope holds of SolidCore's checked Counter. -/
theorem satisfiesEvery : ∃ c, contract? = .ok c ∧
    Satisfies (solidCore fuel) c scopeEvery pre postEvery := by
  obtain ⟨c, hc, -⟩ := satisfies
  exact ⟨c, hc, fun call hs _ => ⟨_, source_run_every hc call hs, rfl⟩⟩

section EveryMIR

open SolarTV SolarTV.Machine

/-- **The lowered MIR on every call of the scope**: stage0 shows expectedEvery, under every
oracle. -/
theorem mir_run_every (o : Oracle) (call : Call) (h : scopeEvery call) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Counter.stage0 call =
      some (expectedEvery call) := by
  rcases call with ⟨cd, v, σ⟩
  obtain ⟨hv, hcl⟩ := h
  dsimp only at hv hcl
  by_cases h0 : v = 0
  swap
  · rw [expectedEvery_value _ h0]
    exact mir_run_value o _ _ h0 hv _
  subst h0
  have hget : (1833756220 : EvmRules.Word) = BitVec.ofNat 256 getSelector := rfl
  have hinc : (2166751455 : EvmRules.Word) = BitVec.ofNat 256 incSelector := rfl
  rcases hcl with ⟨d, rfl⟩ | rfl | hshort | ⟨s, data, hs, rfl, hsel⟩
  · rw [show ({ calldata := (callOf incSelector [d]).calldata, callvalue := 0, storage := σ } : Call) =
      { callOf incSelector [d] with storage := σ } from rfl, expectedEvery_inc d σ]
    exact mir_run_at o d σ
  · rw [show ({ calldata := (callOf getSelector []).calldata, callvalue := 0, storage := σ } : Call) =
      callAt getSelector [] σ from rfl, expectedEvery_get σ]
    refine SolidCore.Refinement.Solar.W1.mir_sem_of_run 9 (mir_run_get_of o _ rfl ?_)
    rw [hget, shr_word0_eq _ _ (by decide)]
    have := selWord_append getSelector (by decide) .empty 0 σ
    rw [← calldata_get] at this
    exact this
  · rw [expectedEvery_short _ hshort rfl]
    obtain ⟨h1, h2⟩ := selWord_short { calldata := cd, callvalue := 0, storage := σ } hshort
    refine SolidCore.Refinement.Solar.W1.mir_sem_of_run 9
      (mir_run_reject_of o _ rfl (Or.inl ⟨?_, ?_⟩))
    · rw [hget, Ne, shr_word0_eq _ _ (by decide)]
      exact h1
    · rw [hinc, Ne, shr_word0_eq _ _ (by decide)]
      exact h2
  · rw [expectedEvery_selector s hs data hsel σ]
    have hw := selWord_append s hs data 0 σ
    refine SolidCore.Refinement.Solar.W1.mir_sem_of_run 9 (mir_run_reject_of o _ rfl ?_)
    rcases hsel with ⟨h1, h2⟩ | ⟨rfl, hlt⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hget, Ne, shr_word0_eq _ _ (by decide), hw]
        exact h2
      · rw [hinc, Ne, shr_word0_eq _ _ (by decide), hw]
        exact h1
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hinc, shr_word0_eq _ _ (by decide), hw]
      · show (selectorOf incSelector ++ data).size < 36
        simp [ByteArray.size_append, size_selectorOf]
        omega

end EveryMIR

/-- **The source stage on every call of the scope**, under every oracle. -/
theorem loweringEvery (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      scopeEvery := by
  intro call hs obs hrun
  change Source.run fuel c call = some obs at hrun
  rw [source_run_every hc call hs] at hrun
  cases hrun
  exact mir_run_every o call hs

/-- **The assembly stage on every call with a value below 2 ^ 256**, whatever its call data
and storage, under every oracle: the generic theorem at check_ok, which holds on every call. -/
theorem assemblyEvery (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code
      (fun call => call.callvalue < 2 ^ 256) :=
  stageAll o _

/-- **The counter on every call.** solar's bytecode for Counter, with the same binding to
solar's exported stages as certified, shows expectedEvery on every call of scopeEvery (inc
and get, with or without value, malformed call data and unknown selectors, from any storage)
under EthLib, through every stage of solar's pipeline. -/
theorem certifiedEvery :
    bytes = SolarTV.Export.Counter.bytecode ∧
    SolarTV.Export.Counter.Manifest.bytecodeHex = runtimeHex ∧
    SolarTV.Export.Counter.Manifest.bytecodeSha256 = runtimeSha256 ∧
    Satisfies ethLib code scopeEvery pre postEvery := by
  refine ⟨bytes_exported, rfl, rfl, ?_⟩
  obtain ⟨c, hc, hspec⟩ := satisfiesEvery
  exact bytecode_of_stages hspec (loweringEvery SolidCore.Refinement.Solar.W1.oracle hc)
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir SolidCore.Refinement.Solar.W1.oracle).mono
      fun _ _ => trivial)
    ((assemblyEvery SolidCore.Refinement.Solar.W1.oracle).mono fun _ h => h.1)

/-- info: 'SolidCore.Refinement.Solar.Counter.certifiedEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedEvery

end SolidCore.Refinement.Solar.Counter
