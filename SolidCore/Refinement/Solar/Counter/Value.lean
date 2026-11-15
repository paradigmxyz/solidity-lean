import SolidCore.Refinement.Solar.Counter.AssemblyAt
import SolidCore.Refinement.Solar.Counter.LoweringAt
import SolidCore.Refinement.Solar.W1Value

/-!
# counter with a nonzero call value

Neither inc nor get is payable, so every call of either that carries value is rejected.
certifiedValue states that solar's bytecode for Counter meets that specification (postValue: the
call reverts with empty output, emits no logs and keeps the call's storage) on scopeValue, every
call of inc on any argument word or of get, with a value v, 0 < v < 2 ^ 256, from any storage,
under EthLib, through every stage of solar's pipeline. It reuses W1Value.lean's approach:

* source: source_run_value_inc and source_run_value_get, SolidCore's dispatcher decodes the
  arguments, finds the function not payable and reverts with empty output (rejectedValueCall?),
  from the run with value v (W1.run_eq_value); satisfiesValue is the specification on SolidCore.
  mir_run_value: solar's first lowered MIR checks the call value first and reverts, on any call
  data and storage. loweringValue is the stage.
* backend: SolarTV.Milestone.Counter.counter_mir_to_evmir, which holds on every call.
* assembly: assemblyValue is the generic theorem, Assemble.stage_of_check_all at check_ok
  (stageAll), which holds on every call with any value from any storage. As a cross-check,
  target_run_value runs EthLib's processMessage of the call directly: the move of v succeeds
  (W1.moveEther_preState), the frame reverts with empty output from every state on every message
  with nonzero value (frame_value: CALLVALUE PUSH1 0x34 JUMPI to JUMPDEST PUSH0 PUSH0 REVERT),
  and processMessage returns that revert (W1.processMessage_reverts_value), on any call data;
  assemblyValue_run is the stage from it.

Not covered: the value's effect on balances (Observable has no balances, and the revert undoes
the move).
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

/-- The frame of Counter's code reverts with empty output from every state on every message
with nonzero value: CALLVALUE PUSH1 0x34 JUMPI jumps to JUMPDEST PUSH0 PUSH0 REVERT. -/
theorem frame_value (msg : Message .fusaka) (hv : msg.value ≠ 0) (st : State.TransactionState)
    (ss : Substate) : Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) Reverted := by
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  repeat symex_one [code, runtimeNat, runtimeSize] [hv] hfork

/-- **EthLib rejects every call of Counter's code with nonzero value**, on any call data and
from any storage: the move of the value succeeds, the frame reverts with empty output, and the
revert undoes the move. -/
theorem target_run_value (cd : ByteArray) (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256)
    (σ : List (Nat × Nat)) :
    Target.run code { calldata := cd, callvalue := v, storage := σ } = some (Abi.rejected σ) := by
  obtain ⟨st', hmove⟩ :=
    W1.moveEther_preState code { calldata := cd, callvalue := v, storage := σ } hv
  obtain ⟨evm, hr, herr, hout⟩ := W1.processMessage_reverts_value
    (Target.message code { calldata := cd, callvalue := v, storage := σ }) rfl rfl
    (W1.ofNat_ne_zero hv0 hv) (precompileAddress_message code _)
    (fun st ss => frame_value _ (W1.ofNat_ne_zero hv0 hv) st ss) _ st' Substate.empty hmove
  simp [Target.run, hr, herr, hout, Abi.rejected]

section ValueMIR

open SolarTV SolarTV.Machine

/-- SolarTV's lowered MIR runs Counter's stage0 on every call with nonzero value, whatever its
call data and storage, to the rejection: entry's call value check reverts with empty output. -/
theorem mir_run_value_of (o : Oracle) (call : Call) (hv0 : call.callvalue ≠ 0)
    (hv : call.callvalue < 2 ^ 256) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (Abi.rejected call.storage) := by
  have hb := W1.ofNat_ne_zero hv0 hv
  repeat (first | sym_eval | simp (config := {decide := true}) only [↓reduceIte])
  have hne : EvmRules.Evm.ne (BitVec.ofNat 256 call.callvalue) 0 = 1 := by
    simp [EvmRules.Evm.ne]
    exact hb
  simp only [hne, show (1 : EvmRules.Word) ≠ 0 by decide, ↓reduceIte]
  repeat sym_eval
  simp [observe, Abi.rejected, Mem.read]

end ValueMIR

/-- The lowered MIR's run with nonzero value, fuel-free. -/
theorem mir_run_value (o : SolarTV.Machine.Oracle) (cd : ByteArray) (v : Nat) (hv0 : v ≠ 0)
    (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    (SolarTV.MIR.Lowered.moduleSem o).run SolarTV.Export.Counter.stage0
        { calldata := cd, callvalue := v, storage := σ } = some (Abi.rejected σ) :=
  W1.mir_sem_of_run 9 (mir_run_value_of o _ hv0 hv)


open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement.Wide
  SolidCore.Refinement.Evm.Wide in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore rejects every call of inc or get with nonzero value, on any argument word, from
any storage: its dispatcher decodes the arguments, finds the function not payable and reverts
with empty output (rejectedValueCall?). -/
theorem source_run_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (sel : Nat) (ws : List U256) (hsel : (sel = incSelector ∧ ws.length = 1) ∨
      (sel = getSelector ∧ ws = [])) (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256)
    (σ : List (Nat × Nat)) :
    Source.run fuel c
        { calldata := (callOf sel ws).calldata, callvalue := v, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  have hd' := Verify.deployedAt_of_deployed hd
  have hcore := hk
  have hm : v % EvmYul.UInt256.size = v := Nat.mod_eq_of_lt hv
  have hw : wordEq v 0 = false := by
    simp [wordEq, Shared.norm, Shared.wordModulus, hm, hv0]
  rw [show (callOf sel ws).calldata = Abi.calldata sel (ws.map (·.toNat)) from rfl,
    W1.run_eq_value hd']
  have hev := hd'.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd'.getElem?_eq_none (by simp)
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m
  rcases hsel with ⟨rfl, hl⟩ | ⟨rfl, rfl⟩
  · match ws, hl with
    | [w], _ =>
      simp only [hcore, List.map_cons, List.map_nil]
      wide_symex [coreLit, fuel, ctxOf, hcore, incSelector, hw]
      simp [Source.observe, Abi.rejected]
  · simp only [hcore, List.map_nil]
    wide_symex [coreLit, fuel, ctxOf, hcore, getSelector, hw]
    simp [Source.observe, Abi.rejected]

/-! ## The value scope through every stage -/

open SolidCore.Refinement.Evm.Wide in
/-- Every call of inc on any argument word, or of get, with a nonzero value v < 2 ^ 256, from
any storage. -/
def scopeValue : Call → Prop := fun call =>
  ∃ (sel : Nat) (ws : List U256) (v : Nat) (σ : List (Nat × Nat)),
    ((sel = incSelector ∧ ws.length = 1) ∨ (sel = getSelector ∧ ws = [])) ∧
    v ≠ 0 ∧ v < 2 ^ 256 ∧
    call = { calldata := (callOf sel ws).calldata, callvalue := v, storage := σ }

/-- Neither function is payable: a call with value reverts with empty output, emits no logs and
keeps the call's storage. -/
def postValue (call : Call) (obs : Observable) : Prop :=
  obs.success = false ∧ obs.output = [] ∧ obs.logs = [] ∧
    ∀ slot, obs.storage slot = slotValue call.storage slot

/-- The specification on the value scope holds of SolidCore's checked Counter. -/
theorem satisfiesValue : ∃ c, contract? = .ok c ∧
    Satisfies (solidCore fuel) c scopeValue pre postValue := by
  obtain ⟨c, hc, -⟩ := satisfies
  refine ⟨c, hc, ?_⟩
  rintro call ⟨sel, ws, v, σ, hsel, hv0, hv, rfl⟩ -
  exact ⟨_, source_run_value hc sel ws hsel v hv0 hv σ, rfl, rfl, rfl, fun _ => rfl⟩

/-- **The source stage on the value scope**, under every oracle. -/
theorem loweringValue (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Counter.stage0 scopeValue := by
  rintro call ⟨sel, ws, v, σ, hsel, hv0, hv, rfl⟩ obs hrun
  change Source.run fuel c _ = some obs at hrun
  rw [source_run_value hc sel ws hsel v hv0 hv σ] at hrun
  cases hrun
  exact mir_run_value o _ v hv0 hv σ

/-- **The assembly stage on the value scope**, under every oracle: the generic theorem for every
program and code the checker accepts, at check_ok, which holds on every call with any value. -/
theorem assemblyValue (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scopeValue :=
  stageAll o scopeValue

/-- The assembly stage on the value scope proved directly, as a cross-check of assemblyValue: the
final EVM IR runs to the rejection (the source stage's MIR run and the backend stages, which hold
on every call), and so does the bytecode on EthLib (target_run_value). -/
theorem assemblyValue_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 code scopeValue := by
  rintro call ⟨sel, ws, v, σ, hsel, hv0, hv, rfl⟩ obs hrun
  have he := SolarTV.Milestone.Counter.counter_mir_to_evmir o _ trivial _
    (mir_run_value o (SolidCore.Refinement.Evm.Wide.callOf sel ws).calldata v hv0 hv σ)
  rw [he] at hrun
  cases hrun
  exact target_run_value _ v hv0 hv σ

/-- **Counter with a nonzero call value**: solar's bytecode for Counter meets the specification
of every call of inc or get with value (neither is payable, so the call is rejected and the
storage kept) under EthLib, through every stage of solar's pipeline. -/
theorem certifiedValue : Satisfies ethLib code scopeValue pre postValue := by
  obtain ⟨c, hc, hspec⟩ := satisfiesValue
  exact bytecode_of_stages hspec (loweringValue W1.oracle hc)
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir W1.oracle).mono fun _ _ => trivial)
    (assemblyValue W1.oracle)

/-- info: 'SolidCore.Refinement.Solar.Counter.certifiedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedValue

end SolidCore.Refinement.Solar.Counter
