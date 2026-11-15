import SolidCore.Refinement.Solar.Counter.AssemblyAt

/-!
# counter: a dropped overflow check is rejected by the source and assembly stages

From the deployed storage the overflow branch of inc is never reached (slot 0 holds 0), so a
compilation that drops the overflow check passes every stage proved on scope. From any
storage (scopeAt) it is reached, and both stages proved there reject such a compilation by a
mismatch of observables on the call inc(1) from storage whose slot 0 holds 2 ^ 256 - 1, where
SolidCore reverts with Panic(0x11) (expectedAt σMax 1):

* loweringAt_rejects: the source stage is false for noCheckStage0, stage0 with both
  arms of the overflow branch going to the store, which stores 0 and succeeds.
* stageAt_rejects: the assembly stage is false for mutantNoCheck, solar's bytecode
  with the overflow check's PUSH1 0x41 JUMPI (offsets 46 to 48) replaced by POP JUMPDEST
  JUMPDEST, so the condition is dropped and the addition's wrapped sum is stored: EthLib runs it
  to a success storing x + d mod 2 ^ 256 from any storage (mutantNoCheck_run_at), every opcode
  stepped by EthLib's program logic, while the final EVM IR reverts (evmir_run_at).
* mutantNoCheck_no_walk: the assembly checker's walk rejects the same bytecode, and
  mutantNoCheck_check the generic checker (Assemble.check, whose acceptance stage_of_check turns
  into the stage) too.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide SolidCore.Refinement.Evm EthLib.Execution EthLib.Execution.Evm
open SolarTV.Milestone.W1

/-- Storage whose slot 0 holds the largest word, so any nonzero addition overflows. -/
def σMax : List (Nat × Nat) := [(0, 2 ^ 256 - 1)]

theorem scopeAt_σMax : scopeAt { callOf incSelector [1] with storage := σMax } :=
  ⟨σMax, ⟨incSelector, [(.uint 256)]⟩, List.mem_singleton_self _, [1], rfl, by simp, rfl⟩

/-- SolidCore's run of inc(1) from σMax fails: the sum overflows. -/
theorem expectedAt_σMax : (expectedAt σMax 1).success = false := by
  simp only [expectedAt, σMax]
  decide

/-! ## The source stage -/

/-- stage0 with the overflow check dropped: both arms of inc's overflow branch go to the store. -/
def noCheckStage0 : SolarTV.MIR.Lowered.Module :=
  { entry := 2,
    functions := [
    -- @inc
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 13) .calldatasize [],
         .pure 15 .lt [.value 13, .const 36]],
        .branch (.value 15) 3 4⟩,
      -- bb1
      ⟨[],
        [.effect none .mstore [.const 32, .const 17],
         .effect none .mstore [.const 0, .const 0x4e487b71]],
        .revert (.const 28) (.const 36)⟩,
      -- bb2
      ⟨[],
        [.effect none .sstore [.const 0, .value 4]],
        .stop⟩,
      -- bb3
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩,
      -- bb4
      ⟨[],
        [.effect (some 17) .calldataload [.const 4],
         .effect (some 2) .sload [.const 0],
         .pure 4 .add [.value 2, .value 17],
         .pure 5 .lt [.value 4, .value 2]],
        .branch (.value 5) 2 2⟩] },
    -- @get
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 2) .sload [.const 0],
         .effect none .mstore [.const 0, .value 2]],
        .ret (.const 0) (.const 32)⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 4 1⟩,
      -- bb1
      ⟨[],
        [.effect (some 4) .calldataload [.const 0],
         .pure 6 .shr [.const 224, .value 4]],
        .switch (.value 6) 4 [(.const 0x6d4ce63c, 2), (.const 0x812600df, 3)]⟩,
      -- bb2
      ⟨[],
        [],
        .tailCall 1 []⟩,
      -- bb3
      ⟨[],
        [],
        .tailCall 0 []⟩,
      -- bb4
      ⟨[],
        [],
        .revert (.const 0) (.const 0)⟩] }] }

/-- What a run of inc(d) from σ shows without the overflow check: success, and slot 0 holding
the wrapped sum. -/
def wrappedAt (σ : List (Nat × Nat)) (d : U256) : Observable :=
  { success := true, output := [], logs := [],
    storage := fun slot =>
      if slot % 2 ^ 256 = 0 then (slotValue σ 0 + d.toNat) % 2 ^ 256 else slotValue σ slot }

section NoCheck

open SolarTV SolarTV.Machine

theorem noCheck_run_of (o : Oracle) (call : Call) (d : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455)
    (h4 : calldataWord call 4 = d) :
    (MIR.Lowered.Module.run o noCheckStage0 call 9).map
        (fun r => observe call r.2 r.1) = some (wrappedAt call.storage d) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte, ite_self])
  have hX : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    simp only [State.initial, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (slotValue_lt _ _)
  simp only [observe, wrappedAt, Option.some.injEq, Observable.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  funext slot
  simp only [storageOf, update]
  split
  · rename_i e
    have h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by simpa using congrArg BitVec.toNat e
    have h' : slot % 2 ^ 256 = 0 := h
    simp only [h', ↓reduceIte, EvmRules.Evm.add, BitVec.toNat_add, hX]
    rw [Nat.add_comm (BitVec.toNat d)]
  · rename_i e
    have h : ¬ slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
    have h' : ¬ slot % 2 ^ 256 = 0 := h
    simp only [h', ↓reduceIte, State.initial, BitVec.toNat_ofNat]
    exact slotValue_mod_mod call.storage slot

theorem noCheck_run_at (o : Oracle) (d : U256) (σ : List (Nat × Nat)) :
    (MIR.Lowered.moduleSem o).run noCheckStage0
        { callOf incSelector [d] with storage := σ } = some (wrappedAt σ d) :=
  SolidCore.Refinement.Solar.W1.mir_sem_of_run 9 (noCheck_run_of o _ d rfl (size_callOf d)
    (by have h := word0 d; rw [show BitVec.ofNat 256 incSelector = 2166751455 from rfl] at h; exact h)
    (word4 d))

end NoCheck

/-- The source stage from any storage is false for the lowering without the overflow check,
under every oracle: on inc(1) from σMax SolidCore reverts, and noCheckStage0 succeeds. -/
theorem loweringAt_rejects (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c noCheckStage0 scopeAt := by
  intro h
  have := h _ scopeAt_σMax _ (source_run_at hc 1 σMax)
  rw [noCheck_run_at] at this
  have hs := congrArg (fun obs : Observable => obs.success) (Option.some.inj this)
  rw [expectedAt_σMax] at hs
  exact absurd hs (by simp [wrappedAt])

/-- info: 'SolidCore.Refinement.Solar.Counter.loweringAt_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms loweringAt_rejects


/-! ## The assembly stage -/

/-- solar's bytecode with the overflow check's PUSH1 0x41 JUMPI (offsets 46 to 48) replaced by
POP JUMPDEST JUMPDEST: the overflow condition is popped and the wrapped sum stored, as big-endian
number. -/
def mutantNoCheckNat : Nat :=
  0x346034575f3560e01c80636d4ce63c146038578063812600df03603457602436106034575f546004358101908110505b5b5f55005b5f5ffd5b5f545f5260205ff35b6011602052634e487b715f526024601cfd

/-- The bytecode with the overflow check dropped, 83 bytes like solar's. -/
def mutantNoCheck : ByteArray :=
  EthLib.Execution.Evm.Logic.NatCode.ofNat mutantNoCheckNat runtimeSize

/-- The mutant is solar's bytecode with offsets 46, 47 and 48 (PUSH1 0x41 JUMPI) replaced by
POP JUMPDEST JUMPDEST, and is otherwise the same. -/
theorem mutantNoCheck_bytes :
    mutantNoCheck.data.toList.map (·.toNat) = ((bytes.set 46 0x50).set 47 0x5b).set 48 0x5b ∧
    bytes[46]? = some 0x60 ∧ bytes[47]? = some 0x41 ∧ bytes[48]? = some 0x57 := by
  decide

/-- The assembly checker's walk rejects the mutant against the final EVM IR. -/
theorem mutantNoCheck_no_walk :
    SolarTV.Assembly.walk (mutantNoCheck.data.toList.map (·.toNat)) SolarTV.Milestone.Counter.offset 0
      SolarTV.Milestone.Counter.items = none := by decide

set_option maxRecDepth 100000 in
/-- The generic checker rejects the mutant: its walk decodes POP where the program has the
overflow check's PUSH1. -/
theorem mutantNoCheck_check :
    Assemble.check SolarTV.Export.Counter.evm5 mutantNoCheck cert = false := by
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.Counter.mutantNoCheck_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutantNoCheck_check

section TargetNoCheck

open EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Symex SolidCore.Refinement.Evm.Logic

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- EthLib runs the mutant on every call of inc(d) from any storage σ to a success that stores
the wrapped sum x + d mod 2 ^ 256 in slot 0, every opcode stepped by EthLib's program logic from
pc 0 with 10M gas. -/
theorem mutantNoCheck_run_at (d : U256) (σ : List (Nat × Nat)) :
    Target.run mutantNoCheck { callOf incSelector [d] with storage := σ } = some (wrappedAt σ d) := by
  refine run_of_postS_at mutantNoCheck incSelector [d] σ _ rfl (fun h => by cases h) ?_
  intro msg hv hd hstat htgt
  simp only [callAt]
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  simp only [incSelector] at hd
  have hval : (BitVec.ofNat 256 (slotValue σ 0) + d).toNat = (slotValue σ 0 + d.toNat) % 2 ^ 256 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := slotValue σ 0) (slotValue_lt σ 0)]
  unfold wrappedAt
  repeat counter_one_at [mutantNoCheck, mutantNoCheckNat, runtimeSize, incSelector] [hd, hv] hfork hstat htgt hval

end TargetNoCheck

/-- The assembly stage from any storage is false for the bytecode without the overflow check,
under every oracle: on inc(1) from σMax the final EVM IR reverts with Panic(0x11), and EthLib
runs the mutant to a success. -/
theorem stageAt_rejects (o : SolarTV.Machine.Oracle) :
    ¬ SolarTV.Stage (SolarTV.evmirSem o) ethLib SolarTV.Export.Counter.evm5 mutantNoCheck scopeAt := by
  intro h
  have := h _ scopeAt_σMax _ (evmir_run_at o 1 σMax)
  change Target.run mutantNoCheck _ = _ at this
  rw [mutantNoCheck_run_at] at this
  have hs := congrArg (fun obs : Observable => obs.success) (Option.some.inj this)
  have he : (expectedAt σMax 1#256).success = false := expectedAt_σMax
  exact absurd hs (by simp [wrappedAt, he])

/-- info: 'SolidCore.Refinement.Solar.Counter.mutantNoCheck_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutantNoCheck_run_at

/-- info: 'SolidCore.Refinement.Solar.Counter.stageAt_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageAt_rejects

end SolidCore.Refinement.Solar.Counter
