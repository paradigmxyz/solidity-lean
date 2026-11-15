import SolidCore.Refinement.Solar.Counter.Lowering
import SolidCore.Refinement.Solar.Counter.SpecAt

/-!
# counter: SolidCore to solar's first lowered MIR, from any storage

The source stage of Counter (Lowering.lean) on `scopeAt` (SpecAt.lean): every call of inc with
any argument word and no value, from any storage `σ`, where slot 0 holds any word `x`, so the
overflow branch is reached when `x + d` does not fit.

* mir_run_of_at: SolarTV's lowered MIR runs stage0 on every such call to `expectedAt σ d`: the
  storage read of `σ`'s slot 0, the overflow check decided by whether `x + d` fits
  (`W1.add_lt_self_iff`), then the write of `x + d` over `σ` or the Panic(0x11) revert that
  keeps `σ`.
* loweringAt: the stage, with source_run_at (SpecAt.lean) for SolidCore.
-/

namespace SolidCore.Refinement.Solar.Counter

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide SolidCore.Refinement.Evm EthLib.Execution EthLib.Execution.Evm
open SolarTV.Milestone.W1

section LoweringAt

open SolarTV SolarTV.Machine

theorem mir_run_of_at (o : Oracle) (call : Call) (d : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 36) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 2166751455)
    (h4 : calldataWord call 4 = d) :
    (MIR.Lowered.Module.run o SolarTV.Export.Counter.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (expectedAt call.storage d) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  have hX : ((State.initial call).storage 0).toNat = slotValue call.storage 0 := by
    simp only [State.initial, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (slotValue_lt _ _)
  by_cases hof : slotValue call.storage 0 + d.toNat < 2 ^ 256
  all_goals
    simp only [add_lt_self_iff_comm, hX, hof, not_true_eq_false,
      not_false_eq_true, ↓reduceIte]
    repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  · simp only [observe, expectedAt, hof, ↓reduceIte, Option.some.injEq, Observable.mk.injEq, true_and]
    refine ⟨rfl, ?_⟩
    funext slot
    simp only [storageOf, update]
    split
    · rename_i e
      have h : slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by simpa using congrArg BitVec.toNat e
      have h' : slot % 2 ^ 256 = 0 := h
      simp only [h', ↓reduceIte, EvmRules.Evm.add, BitVec.toNat_add, hX]
      rw [Nat.add_comm (BitVec.toNat d)]
      exact Nat.mod_eq_of_lt hof
    · rename_i e
      have h : ¬ slot % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := fun h => e (BitVec.eq_of_toNat_eq (by simpa using h))
      have h' : ¬ slot % 2 ^ 256 = 0 := h
      simp only [h', ↓reduceIte, State.initial, BitVec.toNat_ofNat]
      exact slotValue_mod_mod call.storage slot
  · simp only [observe, expectedAt, hof, ↓reduceIte, Option.some.injEq, Observable.mk.injEq]
    refine ⟨trivial, ?_, trivial, trivial⟩
    try simp only [State.initial]
    decide

/-- The same from any storage ¤σ¤: SolarTV's lowered MIR runs stage0 on inc(d) from ¤σ¤ to
¤expectedAt σ d¤, the overflow branch included. -/
theorem mir_run_at (o : Oracle) (d : U256) (σ : List (Nat × Nat)) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Counter.stage0
        { callOf incSelector [d] with storage := σ } = some (expectedAt σ d) :=
  SolidCore.Refinement.Solar.W1.mir_sem_of_run 9 (mir_run_of_at o _ d rfl (size_callOf d)
    (by have h := word0 d; rw [show BitVec.ofNat 256 incSelector = 2166751455 from rfl] at h; exact h)
    (word4 d))

end LoweringAt

/-- **The source stage of Counter from any storage**: SolidCore to solar's first lowered MIR on
every call of inc on any argument word with no value, from any storage, under every oracle. -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      scopeAt := by
  intro call hscope obs hrun
  obtain ⟨d, σ, rfl⟩ := scopeAt_callOf hscope
  change Source.run fuel c { callOf incSelector [d] with storage := σ } = some obs at hrun
  rw [source_run_at hc d σ] at hrun
  cases hrun
  exact mir_run_at o d σ

/-- info: 'SolidCore.Refinement.Solar.Counter.loweringAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt

end SolidCore.Refinement.Solar.Counter
