import SolidCore.Refinement.Solar.W1
import SolidCore.Verify.W5
import W1Proofs.Tactic
import gen.Main.Stage0

/-!
# w5: SolidCore to solar's first lowered MIR

The source stage of the milestone contract w5 (solar's w1),

    contract Main { function f(uint256 a, uint256 b) external pure returns (uint256) {
      return a + b; } }

from SolidCore's checked contract (Corpus.W5.contract?, the type checker's output on the parsed
source, which the kernel checks has the core Corpus.W5.coreLit and deploys to empty storage)
to the first lowered MIR module solar compiles (SolarTV.Export.Main.stage0, after
lower-evm-shaped, so lower-abi's ABI decoding and lower-dispatch's dispatcher included), in
SolarTV's lowered MIR semantics under any oracle.

* mir_run_of: SolarTV's lowered MIR runs stage0, on every call whose call data reads as f(a, b)
  with no value, to expected a b with the call's storage kept (expectedAt), by symbolic
  execution of the module with W1Proofs.Tactic's evaluation steps: entry's callvalue check and selector switch, the tail
  call into f, f's calldatasize check, the two argument loads, the addition and its overflow
  check, and the return of a + b or the Panic(0x11) revert. mir_run is its fuel-free form.
* source_run: SolidCore runs f to the same observable (Verify.W5.run_f, observe_model).
* lowering: the stage on Verify.W5.scope, every call of f on any two argument words with no
  value and empty storage.
* loweringAt: the stage on Verify.W5.scopeAt, the same calls from any storage σ (mir_run_at,
  source_run_at, from Verify.W5.run_f_at), to expectedAt σ a b.
* lowering_rejects_bad: the stage is false for badStage0, stage0 with the addition compiled as
  a subtraction, by the counterexample f(2, 1).

No sorry, native_decide or bv_decide: the theorems depend on propext, Quot.sound and
Classical.choice only (pinned below).
-/

namespace SolidCore.Refinement.Solar.W1

open EthLib.Base SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm.Wide
open SolidCore.Refinement.Wide SolarTV.Milestone.W1

section Lowering

open SolarTV SolarTV.Machine

theorem add_lt_self_iff (a b : EvmRules.Word) :
    (EvmRules.Evm.add a b < a) = ¬ (a.toNat + b.toNat < 2 ^ 256) := by
  unfold EvmRules.Evm.add
  have ha := a.isLt
  have hb := b.isLt
  apply propext
  rw [BitVec.lt_def, BitVec.toNat_add]
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- read_store on a store without the expansion: lowered MIR's `mstore` writes the bytes and
grows the active size in one step, and reads ignore the active size. -/
theorem read_store_mir (m : Mem) (v : EvmRules.Word) :
    ((m.store 0 v).read 0 32).map BitVec.toNat = (natToBytes 32 v.toNat).map (·.toNat) := by
  have e : ((m.store 0 v).expand 0 32).read 0 32 = (m.store 0 v).read 0 32 := by
    unfold Mem.expand; split <;> rfl
  rw [← e]; exact read_store m v

theorem mir_run_of (o : Oracle) (call : Call) (a b : EvmRules.Word) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 68) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 332507694)
    (h4 : calldataWord call 4 = a) (h36 : calldataWord call 36 = b) :
    (MIR.Lowered.Module.run o SolarTV.Export.Main.stage0 call 9).map
        (fun r => observe call r.2 r.1) = some (expectedAt call.storage a b) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
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
      exact slotValue_mod_mod call.storage slot
  · simp only [BitVec.reduceToNat, observe, expectedAt, expected, hof, ↓reduceIte,
      Option.some.injEq, Observable.mk.injEq]
    refine ⟨trivial, ?_, trivial, ?_⟩
    · simp only [State.initial]
      decide
    · trivial

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

/-- SolarTV's lowered MIR semantics runs w5's first lowered MIR module on every call of f(a, b),
under every oracle, to the observable expected a b. -/
theorem mir_run (o : Oracle) (a b : U256) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0 (callOf fSelector [a, b]) =
      some (expected a b) := by
  rw [← expectedAt_nil]
  exact mir_sem_of_run 9 (mir_run_of o _ a b rfl (size_callOf a b) (by rw [word0]; rfl) (word4 a b)
    (word36 a b))

/-- The same from any storage `σ`, which the module keeps. -/
theorem mir_run_at (o : Oracle) (a b : U256) (σ : List (Nat × Nat)) :
    (MIR.Lowered.moduleSem o).run SolarTV.Export.Main.stage0
        { callOf fSelector [a, b] with storage := σ } = some (expectedAt σ a b) :=
  mir_sem_of_run 9 (mir_run_of o _ a b rfl (size_callOf a b)
    (by have h := word0 a b; rw [show BitVec.ofNat 256 fSelector = 332507694 from rfl] at h; exact h)
    (word4 a b) (word36 a b))

end Lowering

/-- The model SolidCore runs f as shows expected a b. -/
theorem observe_model (a b : U256) :
    Verify.observe (fun _ => 0) (Verify.W5.model [a.toNat, b.toNat] (fun _ => 0)) = expected a b := by
  unfold Verify.W5.model expected
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, ↓reduceIte]
    rfl
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, ↓reduceIte]
    rfl

/-- SolidCore runs w5's f on any two argument words to expected a b. -/
theorem source_run {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W5.contract? = .ok c) (a b : U256) :
    Source.run Corpus.W5.fuel c (callOf fSelector [a, b]) = some (expected a b) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W5.shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  rw [show fSelector = Bytecode.W5.Main.fSelector from rfl,
    Verify.W5.run_f hk hd a b, observe_model]

/-- **The source stage of w5**: SolidCore to solar's first lowered MIR, which includes ABI
decoding and dispatch, on every call of f on any two argument words with no value and empty
storage, under every oracle. -/
theorem lowering (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.W5.scope := by
  intro call hscope obs hrun
  obtain ⟨a, b, rfl⟩ := scope_callOf hscope
  change Source.run Corpus.W5.fuel c (callOf fSelector [a, b]) = some obs at hrun
  rw [source_run hc a b] at hrun
  cases hrun
  exact mir_run o a b

/-- The model SolidCore runs f as from any storage `σ` shows expectedAt σ a b. -/
theorem observe_model_at (a b : U256) (σ : List (Nat × Nat)) :
    Verify.observe (slotValue σ) (Verify.W5.model [a.toNat, b.toNat] (slotValue σ)) =
      expectedAt σ a b := by
  unfold Verify.W5.model expectedAt expected
  by_cases h : a.toNat + b.toNat < 2 ^ 256
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, ↓reduceIte]
    rfl
  · simp only [List.getD_cons_zero, List.getD_cons_succ, h, ↓reduceIte]
    rfl

/-- SolidCore runs w5's f on any two argument words from any storage `σ` to expectedAt σ a b. -/
theorem source_run_at {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W5.contract? = .ok c) (a b : U256) (σ : List (Nat × Nat)) :
    Source.run Corpus.W5.fuel c { callOf fSelector [a, b] with storage := σ } =
      some (expectedAt σ a b) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W5.shape_of hc
  obtain ⟨d, hd⟩ := deployed_of hemp
  have := Verify.W5.run_f_at hk (Verify.deployedAt_of_deployed hd) a b σ
  rw [observe_model_at] at this
  exact this

/-- **The source stage of w5 from any storage**: SolidCore to solar's first lowered MIR on every
call of f on any two argument words with no value, from any storage, under every oracle. -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.W5.scopeAt := by
  intro call hscope obs hrun
  obtain ⟨a, b, σ, rfl⟩ := scopeAt_callOf hscope
  change Source.run Corpus.W5.fuel c { callOf fSelector [a, b] with storage := σ } = some obs at hrun
  rw [source_run_at hc a b σ] at hrun
  cases hrun
  exact mir_run_at o a b σ

/-! ## A known-bad lowering is rejected

badStage0 is stage0 with f's addition compiled as a subtraction (value 4 is sub, not add, of
the two argument words): a wrong compilation of the source. lowering_rejects_bad shows the
source stage false for it, by a mismatch of observables: on f(2, 1), SolidCore returns 3,
while badStage0 computes 2 - 1 = 1, which its overflow check (1 < 2) takes for an overflow,
and reverts with Panic(0x11). -/

/-- stage0 with f's addition compiled as a subtraction. -/
def badStage0 : SolarTV.MIR.Lowered.Module :=
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
         .pure 4 .sub [.value 17, .value 19],
         .pure 5 .lt [.value 4, .value 17]],
        .branch (.value 5) 1 2⟩] },
    -- @entry
    { params := [],
      blocks := [
      -- bb0
      ⟨[],
        [.effect (some 0) .callvalue [],
         .ne 2 (.value 0) (.const 0)],
        .branch (.value 2) 3 1⟩,
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

/-- What badStage0 shows on f(2, 1): a revert with Panic(0x11). -/
def badObs : Observable :=
  { success := false,
    output := (natToBytes 4 0x4e487b71).map (·.toNat) ++ (natToBytes 32 0x11).map (·.toNat),
    logs := [], storage := fun _ => 0 }

section Bad

open SolarTV SolarTV.Machine

theorem bad_run_of (o : Oracle) (call : Call) (hv : call.callvalue = 0)
    (hsize : call.calldata.size = 68) (h0 : EvmRules.Evm.shr 224 (calldataWord call 0) = 332507694)
    (h4 : calldataWord call 4 = 2) (h36 : calldataWord call 36 = 1) (hst : call.storage = []) :
    (MIR.Lowered.Module.run o badStage0 call 9).map (fun r => observe call r.2 r.1) =
      some badObs := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | simp (config := {decide := true}) only [↓reduceIte])
  simp only [BitVec.reduceToNat, observe, badObs, Option.some.injEq, Observable.mk.injEq]
  refine ⟨trivial, ?_, trivial, ?_⟩
  · simp only [State.initial]
    decide
  · funext slot
    simp [hst, slotValue]

/-- On f(2, 1), badStage0 reverts with Panic(0x11), the observable of an overflowing call. -/
theorem bad_run (o : Oracle) :
    (MIR.Lowered.moduleSem o).run badStage0 call21 = some badObs :=
  mir_sem_of_run 9 (bad_run_of o _ rfl (size_callOf 2 1) (by rw [call21, word0]; rfl)
    (word4 2 1) (word36 2 1) rfl)

end Bad

/-- The source stage is false for the known-bad lowering, under every oracle: f(2, 1) is in the
scope, SolidCore returns 3 on it, and badStage0 reverts. -/
theorem lowering_rejects_bad (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    ¬ Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c badStage0
      Verify.W5.scope := by
  intro h
  have := h call21 call21_scope (expected 2 1) (source_run hc 2 1)
  rw [bad_run] at this
  have hs := congrArg (fun obs => obs.success) (Option.some.inj this)
  have h21 : (expected 2 1).success = true := by
    have h3 : (2 : U256).toNat + (1 : U256).toNat < 2 ^ 256 := by decide
    simp only [expected, h3, ↓reduceIte]
  rw [h21] at hs
  exact Bool.false_ne_true hs

/-- info: 'SolidCore.Refinement.Solar.W1.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.W1.lowering_rejects_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_rejects_bad

end SolidCore.Refinement.Solar.W1
