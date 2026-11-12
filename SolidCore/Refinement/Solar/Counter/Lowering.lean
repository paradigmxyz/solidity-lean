import SolidCore.Refinement.Solar.Counter.Spec
import SolidCore.Refinement.Solar.Lowering
import counter.gen.Counter.Stage0

/-!
# counter: SolidCore to solar's first lowered MIR

The source stage of Counter (Spec.lean): from SolidCore's checked contract to the first lowered
MIR module solar compiles (SolarTV.Export.Counter.stage0, after lower-evm-shaped, so
lower-abi's ABI decoding and lower-dispatch's dispatcher included), in SolarTV's lowered MIR
semantics under any oracle, on every call of inc with any argument word, no value and empty
storage.

* mir_run_of: SolarTV's lowered MIR runs stage0 on every such call to expected d, by symbolic
  execution of the module (W1Proofs.Tactic's evaluation steps): entry's callvalue check and
  selector switch, the tail call into inc, its calldatasize check, the argument load, the
  storage read, the addition and its overflow check, and the storage write.
* lowering: the stage, with source_run (Spec.lean) for SolidCore.
* lowering_rejects_bad: the stage is false for badStage0, stage0 with the stored word d + 1
  instead of x + d, by the counterexample inc(0).
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide SolidCore.Refinement.Evm EthLib.Execution EthLib.Execution.Evm
open SolarTV.Milestone.W1

section Calldata

open SolarTV SolarTV.Machine SolarTV.EVM.Program

theorem calldata_callOf (d : U256) :
    (callOf incSelector [d]).calldata = cdOf (selectorOf incSelector) [d] := by
  have := calldata_eq_cdOf incSelector [d.toNat] (by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact BitVec.isLt _)
  simpa [callOf, List.map_map, Function.comp_def] using this

theorem word0 (d : U256) :
    EvmRules.Evm.shr 224 (calldataWord (callOf incSelector [d]) 0) = BitVec.ofNat 256 incSelector := by
  rw [SolidCore.Refinement.Solar.W1.calldataWord_eq, calldata_callOf]
  have := shr_cdOf_selectorOf incSelector [d] (by decide)
  simpa [EvmRules.Evm.shr, bitwiseShr] using this

theorem word4 (d : U256) : calldataWord (callOf incSelector [d]) 4 = d := by
  rw [SolidCore.Refinement.Solar.W1.calldataWord_eq, calldata_callOf]
  exact loadWord_cdOf_getD _ [d] 4 (by simp [size_selectorOf]) (by simp [size_selectorOf])
    (by simp [size_selectorOf])

theorem size_callOf (d : U256) : (callOf incSelector [d]).calldata.size = 36 := by
  rw [calldata_callOf, size_cdOf, size_selectorOf]; rfl

end Calldata

section Lowering

open SolarTV SolarTV.Machine

/-- add_lt_self_iff with the addition's operands in the order sym_cond's wordAddComm leaves
them when the first is not the smaller term. -/
theorem add_lt_self_iff_comm (a b : EvmRules.Word) :
    (EvmRules.Evm.add b a < a) = ¬ (a.toNat + b.toNat < 2 ^ 256) := by
  rw [show EvmRules.Evm.add b a = EvmRules.Evm.add a b from BitVec.add_comm b a]
  exact SolidCore.Refinement.Solar.W1.add_lt_self_iff a b

theorem mir_run_of (o : Oracle) (call : Call) (d : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455)
    (h4 : calldataWord call 4 = d) (hst : call.storage = []) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (expected d) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  have hs0 : (State.initial call).storage 0 = 0 := by simp [State.initial, hst, slotValue]
  have hlt : ¬ EvmRules.Evm.add 0 d < 0 := by simp [BitVec.lt_def]
  have hlt' : ¬ EvmRules.Evm.add d 0 < 0 := by simp [BitVec.lt_def]
  simp only [hs0, hlt, hlt', not_false_eq_true, ↓reduceIte]
  repeat (first | sym_eval | sym_cond)
  simp only [observe, expected, Option.some.injEq, Observable.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  funext slot
  simp only [storageOf, update]
  split
  · rename_i e
    have h : slot %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by
      simpa using congrArg BitVec.toNat e
    simp [h, EvmRules.Evm.add]
  · rename_i e
    have h : ¬ slot %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 :=
      fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
    simp [h, State.initial, hst, slotValue]

/-- SolarTV's lowered MIR semantics runs Counter's first lowered MIR module on every call of
inc(d), under every oracle, to the observable expected d. -/
theorem mir_run (o : Oracle) (d : U256) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Counter.stage0 (callOf incSelector [d]) =
      some (expected d) :=
  SolidCore.Refinement.Solar.W1.mir_sem_of_run 9
    (mir_run_of o _ d rfl (size_callOf d) (by rw [word0]; rfl) (word4 d) rfl)

end Lowering

/-- **The source stage of Counter**: SolidCore to solar's first lowered MIR, which includes ABI
decoding and dispatch, on every call of inc on any argument word with no value and empty
storage, under every oracle. -/
theorem lowering (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0 scope := by
  intro call hscope obs hrun
  obtain ⟨d, rfl⟩ := scope_callOf hscope
  change Source.run fuel c (callOf incSelector [d]) = some obs at hrun
  rw [source_run hc d] at hrun
  cases hrun
  exact mir_run o d

/-! ## A known-bad lowering is rejected

badStage0 is stage0 with inc's addition compiled as a subtraction (value 4 is x - d, not x + d):
a wrong compilation of the source. lowering_rejects_bad shows the source stage false for it, by
a mismatch of observables: on inc(1) from empty storage, SolidCore stores 1 in slot 0, while
badStage0 computes 0 - 1 = 2 ^ 256 - 1, which its overflow check (2 ^ 256 - 1 < 0) lets
through, and stores that. -/

/-- stage0 with inc's addition compiled as a subtraction. -/
def badStage0 : SolarTV.MIR.Lowered.Module :=
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
         .pure 4 .sub [.value 2, .value 17],
         .pure 5 .lt [.value 4, .value 2]],
        .branch (.value 5) 1 2⟩] },
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


/-- What badStage0 shows on inc(1): success, and slot 0 holding 2 ^ 256 - 1. -/
def badObs : Observable :=
  { success := true, output := [], logs := [],
    storage := fun slot => if slot % 2 ^ 256 = 0 then 2 ^ 256 - 1 else 0 }

section Bad

open SolarTV SolarTV.Machine

theorem bad_run_of (o : Oracle) (call : Call) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455)
    (h4 : calldataWord call 4 = 1) (hst : call.storage = []) :
    (MIR.Lowered.Module.run o badStage0 call 9).map (fun r => observe call r.2 r.1) =
      some badObs := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  have hs0 : (State.initial call).storage 0 = 0 := by simp [State.initial, hst, slotValue]
  have hlt : ¬ EvmRules.Evm.sub 0 1 < 0 := by simp [BitVec.lt_def]
  simp only [hs0, hlt, not_false_eq_true, ↓reduceIte]
  repeat (first | sym_eval | sym_cond)
  simp only [observe, badObs, Option.some.injEq, Observable.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  funext slot
  simp only [storageOf, update]
  split
  · rename_i e
    have h : slot %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by
      simpa using congrArg BitVec.toNat e
    simp [h]
    all_goals decide
  · rename_i e
    have h : ¬ slot %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 :=
      fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
    simp [h, State.initial, hst, slotValue]

/-- On inc(1), badStage0 stores 2 ^ 256 - 1. -/
theorem bad_run (o : Oracle) :
    (MIR.Lowered.moduleSem o).run badStage0 (callOf incSelector [1]) = some badObs :=
  SolidCore.Refinement.Solar.W1.mir_sem_of_run 9
    (bad_run_of o _ rfl (size_callOf 1) (by rw [word0]; rfl) (word4 1) rfl)

end Bad

theorem inc1_scope : scope (callOf incSelector [1]) :=
  ⟨⟨incSelector, [(.uint 256)]⟩, List.mem_singleton_self _, [1], rfl, by simp, rfl⟩

/-- The source stage is false for the known-bad lowering, under every oracle: inc(1) is in the
scope, SolidCore stores 1 on it, and badStage0 stores 2 ^ 256 - 1. -/
theorem lowering_rejects_bad (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c badStage0 scope := by
  intro h
  have := h _ inc1_scope (expected 1) (source_run hc 1)
  rw [bad_run] at this
  have hs := congrArg (fun obs => obs.storage 0) (Option.some.inj this)
  simp only [badObs, expected] at hs
  exact absurd hs (by decide)

/-- info: 'SolidCore.Refinement.Solar.Counter.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.Counter.lowering_rejects_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_rejects_bad

end SolidCore.Refinement.Solar.Counter
