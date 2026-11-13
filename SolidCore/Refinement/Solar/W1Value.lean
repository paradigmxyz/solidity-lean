import SolidCore.Refinement.Solar.Milestone

/-!
# w1 with a nonzero call value

f is not payable, so every call of it that carries value is rejected. certifiedValue states that
solar's bytecode for w1 meets that specification (postValue: the call reverts with empty output,
emits no logs and keeps the call's storage) on scopeValue, every call of f on any two argument
words with a value v, 0 < v < 2 ^ 256, from any storage, under EthLib, through every stage of
solar's pipeline:

* source: source_run_value, SolidCore's dispatcher decodes the arguments, finds f not payable
  and reverts with empty output (rejectedValueCall?); run_eq_value runs Source.run with value v
  (the constructor runs with no value whatever the call's, so DeployedAt still applies), and
  satisfiesValue is the specification on SolidCore. mir_run_value: solar's first lowered MIR
  checks the call value first and reverts, on any call data and storage. loweringValue is the
  stage.
* backend: SolarTV.Milestone.W1.w1_mir_to_evmir, which holds on every call (any call data, call
  value and storage).
* assembly: assemblyValue is the generic theorem, Assemble.stage_of_check_all at check_ok, which
  holds on every call with any value from any storage. As a cross-check, target_run_value runs
  EthLib's processMessage of the call directly: the move of v from the caller (which holds
  exactly v) to the contract succeeds (moveEther_preState), the frame reverts with empty output
  from every state on every message with nonzero value (frame_value: CALLVALUE PUSH1 0x2e JUMPI
  to JUMPDEST PUSH0 PUSH0 REVERT, every opcode stepped by EthLib's program logic), and
  processMessage returns that revert (processMessage_reverts_value), on any call data;
  assemblyValue_run is the stage from it.

loweringValue_rejects: the source stage on scopeValue is false for noValueStage0, stage0 with
the call value check dropped, by a mismatch of observables on f(1, 2) with value 1, where
SolidCore rejects the call and noValueStage0 returns 3.

Not covered: the value's effect on balances (Observable has no balances, and the revert undoes
the move), and payable functions, which w1 has none of.
-/

namespace SolidCore.Refinement.Solar.W1

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

/-- A message that moves nonzero value, to code that is no precompile, whose frame reverts with
empty output from every state: once the move of its value succeeds, processMessage at Fusaka
returns the revert with empty output. -/
theorem processMessage_reverts_value {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (htr : message.shouldTransferValue = true)
    (hv : message.value ≠ 0) (hpre : precompileAddress .fusaka message = none)
    (h : ∀ st ss, Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) Reverted)
    (st st' : State.TransactionState) (ss : Substate)
    (hmove : st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st') :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = some .revert ∧ evm.1.output = .empty := by
  rw [processMessage]
  have hss : startState .fusaka message st = st := by
    simp [startState, show ¬ (Fork.fusaka < Fork.paris) by decide]
  simp only [hss, hpre, htr, ne_eq, hv, not_false_eq_true, and_self, ↓reduceIte, hmove]
  simp only [pure, Except.pure, bind, Except.bind, Except.mapError]
  split
  · rename_i e hr
    obtain ⟨after, h', -⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
  · rename_i after hr
    obtain ⟨after', h', -, herr, hout⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> simp [hout]


/-- The call value as a word is nonzero. -/
theorem ofNat_ne_zero {v : Nat} (hv0 : v ≠ 0) (hv : v < 2 ^ 256) : BitVec.ofNat 256 v ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
  exact hv0 this

/-- A choice between two successes succeeds. -/
theorem exists_ite_pure {ε α : Type} (c : Prop) [Decidable c] (a b : α) :
    ∃ x, (if c then (pure a : Except ε α) else pure b) = .ok x :=
  ⟨if c then a else b, by split <;> rfl⟩

open EthLib.Execution.State in
/-- The caller of a call holds exactly its value, and the contract holds none: moving the value
from the caller to the contract succeeds. -/
theorem moveEther_preState (code : ByteArray) (call : Call) (hv : call.callvalue < 2 ^ 256) :
    ∃ st', (Target.preState code call).moveEther .fusaka (Target.address callerAddress)
      (Target.address selfAddress) (BitVec.ofNat 256 call.callvalue) = .ok st' := by
  simp only [TransactionState.moveEther, TransactionState.modifyState, bind, Except.bind]
  have hAB : Target.address callerAddress ≠ Target.address selfAddress := by decide
  simp [TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.recordAccountRead, TransactionState.setAccount, Target.preState,
    TransactionState.ofBlock, State.getAccountOptional, Account.debit, Account.credit,
    TransactionState.destroyAccount, hAB.symm, BitVec.toNat_ofNat]
  have hv' : call.callvalue %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        call.callvalue := Nat.mod_eq_of_lt hv
  have hv2 : call.callvalue <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := hv
  split_ifs
  all_goals
    simp [hv', hv2, Std.ExtTreeMap.getElem_insert, Std.ExtTreeMap.getElem_insert_self,
      pure, Except.pure, TransactionState.destroyStorage, hAB, BitVec.toNat_ofNat]
  all_goals exact exists_ite_pure _ _ _

/-- The frame of w1's code reverts with empty output from every state on every message with
nonzero value: CALLVALUE PUSH1 0x2e JUMPI jumps to JUMPDEST PUSH0 PUSH0 REVERT. -/
theorem frame_value (msg : Message .fusaka) (hv : msg.value ≠ 0) (st : State.TransactionState)
    (ss : Substate) : Spec .fusaka (At code msg 0 [] .empty 10000000 st ss .empty) Reverted := by
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  repeat symex_one [code, runtimeNat, runtimeSize] [hv] hfork


section ValueMIR

open SolarTV SolarTV.Machine

/-- SolarTV's lowered MIR runs w1's stage0 on every call with nonzero value, whatever its call
data and storage, to the rejection: entry's call value check reverts with empty output. -/
theorem mir_run_value_of (o : Oracle) (call : Call) (hv0 : call.callvalue ≠ 0)
    (hv : call.callvalue < 2 ^ 256) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (Abi.rejected call.storage) := by
  have hb := ofNat_ne_zero hv0 hv
  repeat (first | sym_eval | simp (config := {decide := true}) only [↓reduceIte])
  have hne : EvmRules.Evm.ne (BitVec.ofNat 256 call.callvalue) 0 = 1 := by
    simp [EvmRules.Evm.ne]
    exact hb
  simp only [hne, show (1 : EvmRules.Word) ≠ 0 by decide, ↓reduceIte]
  repeat sym_eval
  simp [observe, Abi.rejected, Mem.read]

end ValueMIR


/-- **EthLib rejects every call of w1's code with nonzero value**, on any call data and from any
storage: the move of the value succeeds, the frame reverts with empty output, and the revert
undoes the move. -/
theorem target_run_value (cd : ByteArray) (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256)
    (σ : List (Nat × Nat)) :
    Target.run code { calldata := cd, callvalue := v, storage := σ } = some (Abi.rejected σ) := by
  obtain ⟨st', hmove⟩ := moveEther_preState code { calldata := cd, callvalue := v, storage := σ } hv
  obtain ⟨evm, hr, herr, hout⟩ := processMessage_reverts_value
    (Target.message code { calldata := cd, callvalue := v, storage := σ }) rfl rfl
    (ofNat_ne_zero hv0 hv) (precompileAddress_message code _)
    (fun st ss => frame_value _ (ofNat_ne_zero hv0 hv) st ss) _ st' Substate.empty hmove
  simp [Target.run, hr, herr, hout, Abi.rejected]

/-- The lowered MIR's run, fuel-free. -/
theorem mir_run_value (o : SolarTV.Machine.Oracle) (cd : ByteArray) (v : Nat) (hv0 : v ≠ 0)
    (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    (SolarTV.MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0
        { calldata := cd, callvalue := v, storage := σ } = some (Abi.rejected σ) :=
  mir_sem_of_run 9 (mir_run_value_of o _ hv0 hv)

open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement.Wide in
/-- Source.run of a call with value v from the storage σ, once the constructor's result is
known: the constructor runs with no value whatever the call's (constructWithContext? sets it),
so it is the deployed state, and the ABI dispatcher of the core contract runs with v. -/
theorem run_eq_value {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : DeployedAt fuel c d s) (sel : Nat) (ws : List U256)
    (v : Nat) (σ : List (Nat × Nat)) :
    Source.run fuel c
        { calldata := Abi.calldata sel (ws.map (·.toNat)), callvalue := v, storage := σ } =
      Option.map (Source.observe
          { calldata := Abi.calldata sel (ws.map (·.toNat)), callvalue := v, storage := σ })
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core { ctxOf c with value := v }
          { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress callerAddress v
          ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  have hc' : TypeCheck.CheckedContract.constructWithContext? fuel c
      { c.core.context with sender := callerAddress, self := selfAddress, value := v }
      State.empty selfAddress 0 [] = some (CallResult.returned d vs) := hc
  simp only [Source.run, Source.result?]
  rw [hc']
  simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?, Dirty.bytes_calldata]
  rfl


open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement.Wide
  SolidCore.Refinement.Evm.Wide in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- SolidCore rejects every call of w5's f with nonzero value, on any argument words, from any
storage: its dispatcher decodes the arguments, finds f not payable and reverts with empty
output (rejectedValueCall?). -/
theorem source_run_value {c : TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c)
    (a b : U256) (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    Source.run Corpus.W5.fuel c
        { calldata := (callOf fSelector [a, b]).calldata, callvalue := v, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W5.shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  have hd' := Verify.deployedAt_of_deployed hd
  have hcore := hk
  have hm : v % EvmYul.UInt256.size = v := Nat.mod_eq_of_lt hv
  have hw : wordEq v 0 = false := by
    simp [wordEq, Shared.norm, Shared.wordModulus, hm, hv0]
  rw [show (callOf fSelector [a, b]).calldata =
    Abi.calldata Bytecode.W5.Main.fSelector ([a, b].map (·.toNat)) from rfl, run_eq_value hd']
  have hev := hd'.events
  have h0 : ∀ q : Nat, d.storage[q]? = none := fun q => hd'.getElem?_eq_none (by simp)
  generalize σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage = m
  simp only [hcore, List.map_cons, List.map_nil]
  wide_symex [Corpus.W5.coreLit, Corpus.W5.fuel, ctxOf, hcore, Bytecode.W5.Main.fSelector, hw]
  simp [Source.observe, Abi.rejected]


/-! ## The value scope through every stage -/

open SolidCore.Refinement.Evm.Wide in
/-- Every call of f on any two argument words with a nonzero value v < 2 ^ 256, from any
storage. -/
def scopeValue : Call → Prop := fun call =>
  ∃ (a b : U256) (v : Nat) (σ : List (Nat × Nat)), v ≠ 0 ∧ v < 2 ^ 256 ∧
    call = { calldata := (callOf fSelector [a, b]).calldata, callvalue := v, storage := σ }

/-- f is not payable: a call with value reverts with empty output, emits no logs and keeps the
call's storage. -/
def postValue (call : Call) (obs : Observable) : Prop :=
  obs.success = false ∧ obs.output = [] ∧ obs.logs = [] ∧
    ∀ slot, obs.storage slot = slotValue call.storage slot

/-- No precondition beyond the scope. -/
def preValue : Call → Prop := fun _ => True

/-- The specification on the value scope holds of SolidCore's checked w5. -/
theorem satisfiesValue : ∃ c, Corpus.W5.contract? = .ok c ∧
    Satisfies (solidCore Corpus.W5.fuel) c scopeValue preValue postValue := by
  obtain ⟨c, hc, -⟩ := Verify.W5.satisfies
  refine ⟨c, hc, ?_⟩
  rintro call ⟨a, b, v, σ, hv0, hv, rfl⟩ -
  exact ⟨_, source_run_value hc a b v hv0 hv σ, rfl, rfl, rfl, fun _ => rfl⟩

/-- **The source stage on the value scope**, under every oracle. -/
theorem loweringValue (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 scopeValue := by
  rintro call ⟨a, b, v, σ, hv0, hv, rfl⟩ obs hrun
  change Source.run Corpus.W5.fuel c _ = some obs at hrun
  rw [source_run_value hc a b v hv0 hv σ] at hrun
  cases hrun
  exact mir_run_value o _ v hv0 hv σ

/-- **The assembly stage on the value scope**, under every oracle: the generic theorem for every
program and code the checker accepts, at check_ok, which holds on every call with any value. -/
theorem assemblyValue (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scopeValue :=
  Assemble.stage_of_check_all check_ok o scopeValue

/-- The assembly stage on the value scope proved directly, as a cross-check of assemblyValue:
the final EVM IR runs to the rejection (the source stage's MIR run and the backend stages, which
hold on every call), and so does the bytecode on EthLib (target_run_value). -/
theorem assemblyValue_run (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) ethLib program code scopeValue := by
  rintro call ⟨a, b, v, σ, hv0, hv, rfl⟩ obs hrun
  have he := SolarTV.Milestone.W1.w1_mir_to_evmir o _ trivial _
    (mir_run_value o (SolidCore.Refinement.Evm.Wide.callOf fSelector [a, b]).calldata v hv0 hv σ)
  rw [show program = SolarTV.Export.Main.evm4 from rfl, he] at hrun
  cases hrun
  exact target_run_value _ v hv0 hv σ

/-- **w1 with a nonzero call value**: solar's bytecode for w1 meets f's specification on every
call with value (it is not payable, so the call is rejected and the storage kept) under
EthLib, through every stage of solar's pipeline. -/
theorem certifiedValue : Satisfies ethLib code scopeValue preValue postValue := by
  obtain ⟨c, hc, hspec⟩ := satisfiesValue
  exact bytecode_of_stages hspec (loweringValue oracle hc)
    ((SolarTV.Milestone.W1.w1_mir_to_evmir oracle).mono fun _ _ => trivial) (assemblyValue oracle)

/-- info: 'SolidCore.Refinement.Solar.W1.certifiedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedValue

/-- info: 'SolidCore.Refinement.Solar.W1.target_run_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms target_run_value

/-- info: 'SolidCore.Refinement.Solar.W1.source_run_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_run_value

/-- info: 'SolidCore.Refinement.Solar.W1.loweringValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loweringValue

/-- info: 'SolidCore.Refinement.Solar.W1.assemblyValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assemblyValue


/-! ## A lowering without the call value check is rejected

noValueStage0 is stage0 with entry's call value check dropped (both arms of its branch go on
to the selector switch), so f runs whatever the value. loweringValue_rejects shows the source
stage on the value scope false for it, by a mismatch of observables: on f(1, 2) with value 1,
SolidCore rejects the call and noValueStage0 returns 3. -/

/-- stage0 with the call value check dropped. -/
def noValueStage0 : SolarTV.MIR.Lowered.Module :=
  { entry := 1,
    functions := [
    -- @f
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 13) .calldatasize [],
         .pure 15 .lt [.value 13, .const 68]],
        .branch (.value 15) 3 4⟩,
      -- bb1
      ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩,
      -- bb2
      ⟨[],
        [.effect none .mstore [.const 0, .value 4]],
        .ret (.const 0) (.const 32)⟩,
      -- bb3
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb4
      ⟨[],
        [.effect (some 17) .calldataload [.const 4],
         .effect (some 19) .calldataload [.const 36],
         .pure 4 .add [.value 17, .value 19],
         .pure 5 .lt [.value 4, .value 17]],
        .branch (.value 5) 1 2⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 1 1⟩,
      -- bb1
      ⟨[],
        [.effect (some 4) .calldataload [.const 0],
         .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 3 [(.const 0x13d1aa2e, 2)]⟩,
      -- bb2
      ⟨[],
        [],
        .tailCall 0 []⟩,
      -- bb3
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩] }] }

section NoValue

open SolarTV SolarTV.Machine SolarTV.Milestone.W1

/-- noValueStage0 runs f on every call of f(a, b), whatever its value, as stage0 does on calls
with no value. -/
theorem noValue_run_of (o : Oracle) (call : Call) (a b : EvmRules.Word)
    (hsize : call.calldata.size = 68) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 332507694)
    (h4 : calldataWord call 4 = a) (h36 : calldataWord call 36 = b) :
    (MIR.Lowered.Module.run o noValueStage0 call 9).map
        (fun r => observe call r.2 r.1) = some (expectedAt call.storage a b) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, ite_self])
  by_cases hof : a.toNat + b.toNat < 2 ^ 256
  all_goals
    simp only [add_lt_self_iff, hof, not_true_eq_false, not_false_eq_true, ↓reduceIte]
    repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  · simp only [BitVec.reduceToNat, observe, expectedAt, expected, hof, ↓reduceIte,
      Option.some.injEq, Observable.mk.injEq, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [read_store_mir]
      simp only [EvmRules.Evm.add, BitVec.toNat_add, Nat.mod_eq_of_lt hof]
    · rfl
    · funext slot
      simp [storageOf, State.initial]
      exact SolidCore.Refinement.Evm.Wide.slotValue_mod_mod call.storage slot
  · simp only [BitVec.reduceToNat, observe, expectedAt, expected, hof, ↓reduceIte,
      Option.some.injEq, Observable.mk.injEq]
    refine ⟨trivial, ?_, trivial, ?_⟩
    · try simp only [State.initial]
      decide
    · trivial

end NoValue

open SolidCore.Refinement.Evm.Wide in
/-- The source stage on the value scope is false for the lowering without the call value check,
under every oracle: on f(1, 2) with value 1 from empty storage SolidCore rejects the call, and
noValueStage0 succeeds. -/
theorem loweringValue_rejects (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    ¬ Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c noValueStage0
      scopeValue := by
  intro h
  have hs : scopeValue
      { calldata := (callOf fSelector [1, 2]).calldata, callvalue := 1, storage := [] } :=
    ⟨1, 2, 1, [], by decide, by decide, rfl⟩
  have := h _ hs _ (source_run_value hc 1 2 1 (by decide) (by decide) [])
  have hrun : (SolarTV.MIR.Lowered.moduleSem o).run noValueStage0
      { calldata := (callOf fSelector [1, 2]).calldata, callvalue := 1, storage := [] } =
        some (expectedAt [] 1 2) :=
    mir_sem_of_run 9 (noValue_run_of o _ 1 2 (size_callOf 1 2)
      (by have h := word0 1 2; rw [show BitVec.ofNat 256 fSelector = 332507694 from rfl] at h; exact h)
      (word4 1 2) (word36 1 2))
  rw [hrun] at this
  have hsucc := congrArg (fun obs : Observable => obs.success) (Option.some.inj this)
  simp [expectedAt, expected, Abi.rejected] at hsucc

/-- info: 'SolidCore.Refinement.Solar.W1.loweringValue_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loweringValue_rejects

end SolidCore.Refinement.Solar.W1
