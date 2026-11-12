import SolidCore.Refinement.Solar.Counter.Value
import SolidCore.Refinement.Solar.Counter.Assembly

/-!
# counter: a wrong call value check in the bytecode is rejected

mutantValue is solar's bytecode with the call value check's jump target (offset 2, the PUSH1
operand 0x34 of CALLVALUE PUSH1 0x34 JUMPI) changed to 0x41, the Panic(0x11) block: on a call
with no value it behaves as solar's bytecode, and on a call with value it reverts with
Panic(0x11) instead of empty output. The assembly stage on the value scope (Value.lean) is false
for it by a mismatch of observables: on get() with value 1 from empty storage the final EVM IR
rejects the call with empty output, while EthLib runs the mutant to a revert with Panic(0x11)
(mutantValue_run, every opcode stepped by EthLib's program logic after the move of the value).
The assembly checker's walk and the generic checker reject it too (mutantValue_no_walk,
mutantValue_check), and its sha256 is not the pinned one (milestone.sh).
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Wide

/-- solar's bytecode with the call value check jumping to the Panic(0x11) block (offset 2, 0x34
to 0x41), as big-endian number. -/
def mutantValueNat : Nat :=
  0x346041575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f5460043581019081106041575f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd

/-- The bytecode with the call value check retargeted, 83 bytes like solar's. -/
def mutantValue : ByteArray :=
  EthLib.Execution.Evm.Logic.NatCode.ofNat mutantValueNat runtimeSize

/-- The mutant is solar's bytecode with offset 2 (the value check's jump target 0x34) set to
0x41, and is otherwise the same. -/
theorem mutantValue_bytes :
    mutantValue.data.toList.map (·.toNat) = bytes.set 2 0x41 ∧ bytes[2]? = some 0x34 := by
  decide

/-- The assembly checker's walk rejects the mutant against the final EVM IR. -/
theorem mutantValue_no_walk :
    SolarTV.Assembly.walk (mutantValue.data.toList.map (·.toNat))
      SolarTV.Milestone.Counter.offset 0 SolarTV.Milestone.Counter.items = none := by decide

set_option maxRecDepth 100000 in
/-- The generic checker rejects the mutant: the value check's PUSH1 pushes 0x41, not the
offset of the block it jumps to in the final EVM IR. -/
theorem mutantValue_check :
    Assemble.check SolarTV.Export.Counter.evm5 mutantValue cert = false := by
  decide +kernel

/-- What the mutant shows on a call with value from the storage σ: a revert with Panic(0x11)
that keeps σ. -/
def panicked (σ : List (Nat × Nat)) : Observable :=
  { success := false, output := Verify.panic 0x11, logs := [], storage := slotValue σ }

/-- A message that moves nonzero value, to code that is no precompile, whose frame fails as
PostS X says from every state: once the move of its value succeeds, processMessage at Fusaka
returns the revert with X's output. -/
theorem processMessage_postS_value {c : ByteArray} (message : Message .fusaka)
    (hcode : message.code = c) (htr : message.shouldTransferValue = true)
    (hv : message.value ≠ 0) (hpre : precompileAddress .fusaka message = none) (X : Observable)
    (hX : X.success = false)
    (h : ∀ st ss, Spec .fusaka (At c message 0 [] .empty message.gas st ss .empty) (PostS X ss))
    (st st' : State.TransactionState) (ss : Substate)
    (hmove : st.moveEther .fusaka message.caller message.currentTarget message.value = .ok st') :
    ∃ evm, processMessage (Meter := Nat) .fusaka message st ss = .ok evm ∧
      evm.1.error = some .revert ∧ evm.1.output.toList.map (·.toNat) = X.output := by
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
    obtain ⟨after', h', -, herr, hout, -⟩ := runFrame_of_spec hcode (h _ _) hr
    cases h'
    simp only [errorOf, hX, Bool.false_eq_true, ↓reduceIte] at herr
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [rollbackOnError]; split <;> simp [herr]
    · simp only [rollbackOnError]; split <;> exact hout

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The mutant's frame on every message with nonzero value, from every state: CALLVALUE PUSH1
0x41 JUMPI jumps to the Panic(0x11) block, which reverts with Panic(0x11). -/
theorem mutantValue_frame (msg : Message .fusaka) (hv : msg.value ≠ 0)
    (st : State.TransactionState) (ss : Substate) :
    Spec .fusaka (At mutantValue msg 0 [] .empty 10000000 st ss .empty)
      (PostS (panicked []) ss) := by
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  unfold panicked
  repeat counter_one_at [mutantValue, mutantValueNat, runtimeSize] [hv] hfork hfork hfork hfork

/-- EthLib runs the mutant on every call with nonzero value, on any call data and from any
storage σ, to a revert with Panic(0x11) that keeps σ. -/
theorem mutantValue_run (cd : ByteArray) (v : Nat) (hv0 : v ≠ 0) (hv : v < 2 ^ 256)
    (σ : List (Nat × Nat)) :
    Target.run mutantValue { calldata := cd, callvalue := v, storage := σ } =
      some (panicked σ) := by
  obtain ⟨st', hmove⟩ :=
    W1.moveEther_preState mutantValue { calldata := cd, callvalue := v, storage := σ } hv
  obtain ⟨evm, hr, herr, hout⟩ := processMessage_postS_value
    (Target.message mutantValue { calldata := cd, callvalue := v, storage := σ }) rfl rfl
    (W1.ofNat_ne_zero hv0 hv) (precompileAddress_message mutantValue _) (panicked []) rfl
    (fun st ss => mutantValue_frame _ (W1.ofNat_ne_zero hv0 hv) st ss) _ st' Substate.empty hmove
  simp only [panicked] at hout
  simpa [Target.run, hr, herr, panicked] using hout

/-- The assembly stage on the value scope is false for the mutant, under every oracle: on get()
with value 1 from empty storage the final EVM IR rejects the call with empty output, and EthLib
runs the mutant to a revert with Panic(0x11). -/
theorem assemblyValue_rejects (o : SolarTV.Machine.Oracle) :
    ¬ SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 mutantValue
      scopeValue := by
  intro h
  have hs : scopeValue { calldata := (callOf getSelector []).calldata, callvalue := 1, storage := [] } :=
    ⟨getSelector, [], 1, [], Or.inr ⟨rfl, rfl⟩, by decide, by decide, rfl⟩
  have he := SolarTV.Milestone.Counter.counter_mir_to_evmir o _ trivial _
    (mir_run_value o (callOf getSelector []).calldata 1 (by decide) (by decide) [])
  have := h _ hs _ he
  change Target.run mutantValue _ = _ at this
  rw [mutantValue_run _ 1 (by decide) (by decide) []] at this
  have ho := congrArg (fun obs : Observable => obs.output) (Option.some.inj this)
  simp only [panicked, Abi.rejected, Verify.panic, Verify.word] at ho
  have hl := congrArg List.length ho
  simp [natToBytes_length] at hl

/-- info: 'SolidCore.Refinement.Solar.Counter.mutantValue_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutantValue_check

/-- info: 'SolidCore.Refinement.Solar.Counter.assemblyValue_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assemblyValue_rejects

end SolidCore.Refinement.Solar.Counter
