import Verify.Phase3.RecSum.Bytecode
import Verify.Phase3.RecSource.Join

/-!
# RecSum: a concrete gas bound, from the final EVM IR's block count

`total_returns_bytecode` gives the bytecode's result from an existential gas `G` on each
call: the assembly checker's bound `gasBoundL cert n` for a block count `n` that the backend stages'
forward simulation only shows to exist. Here the count is computed on the final EVM IR itself
(`evm6`): the recursive function's blocks run `2 * v + 2` times from an entry at measure `v` (by
induction on `v`, `fn_steps`), so a call of `total(a)`, `a ≤ 64`, ends within `2 * a + 4` blocks
(`ends_within`). With `gasBoundL cert n = 618800 * n + 9` (`gasBound_eq`) the bytecode returns
`a * (a + 1) / 2` at every gas from `618800 * (2 * a + 4) + 9` on (`bytecode_gas`), at most
`81681609` for every `a ≤ 64`. `source_to_bytecode_gas` is the source theorem with that bound.

A limit of the assembly certificate, as review 193 noted: its frame set (`frames.blocks = [1, 4, 5]`)
is not closed under the program's edges. Block 4's overflow branch goes to block 6, the
`Panic(0x11)` block, which is outside the frames and stores to memory. `checkF` checks block 6 as an
ordinary block (it ends the run with a revert, so no frame is returned through), which is sound for
the forward result, but "the function's blocks are stack-only" covers only the framed blocks, not
every block the function can reach.
-/

namespace Verify.Phase3.RecSource.Gas
open SolarTV SolarTV.Machine SolarTV.Export.RecSum SolarTV.Milestone.W1
open SolarTV.Milestone.RecSum (steps_mk steps_zero sub_one_ofNat add_ofNat lt_add_ofNat tri_succ tri_le)

theorem ovf_false {n : Nat} (h : n ≤ 1024) : (1024 < n) = False := by
  simp only [eq_iff_iff, iff_false, Nat.not_lt]; exact h

set_option hygiene false in
/-- Run blocks of `evm6` by their definitions, with the stack-height checks decided by `omega`. -/
macro "evm_run" : tactic => `(tactic| (
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | simp only [steps_mk, steps_zero] | sym_eval | simp (disch := omega) only [ovf_false, List.length_cons, ↓reduceIte, ite_false, ite_true] | sym_cond | sym_mem)))

/-- Measure 0: block 1 sees `n = 0` and block 5 returns 0 to the frame's label. -/
theorem fn_zero (o : Oracle) (call : Call) (L : EvmRules.Word) (T : EVM.Stack) (s : State)
    (hT : T.length ≤ 900) :
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) 2 (1, L :: BitVec.ofNat 256 0 :: T, s) =
      some (.inr (L.toNat, BitVec.ofNat 256 0 :: T, s)) := by
  evm_run
  all_goals (try rfl)

/-- Measure `m + 1`: block 1 calls the function at `m` with return label 4, keeping the caller's
label and the argument. -/
theorem fn_call (o : Oracle) (call : Call) (L : EvmRules.Word) (T : EVM.Stack) (s : State) (m : Nat)
    (hm : m + 1 ≤ 64) (hT : T.length ≤ 900) :
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) 1 (1, L :: BitVec.ofNat 256 (m + 1) :: T, s) =
      some (.inr (1, BitVec.ofNat 256 4 :: BitVec.ofNat 256 m :: L :: BitVec.ofNat 256 (m + 1) :: T, s)) := by
  have hz : (BitVec.ofNat 256 (m + 1) = 0) = False := by
    simp only [eq_iff_iff, iff_false]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  have hs := sub_one_ofNat m (by omega)
  evm_run
  all_goals (try rfl)

/-- Block 4: the caller resumes with the callee's result `t`, adds its argument and returns. -/
theorem fn_resume (o : Oracle) (call : Call) (L : EvmRules.Word) (T : EVM.Stack) (s : State) (m t : Nat)
    (ht : t + (m + 1) < 2 ^ 256) (hT : T.length ≤ 900) :
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) 1 (4, BitVec.ofNat 256 t :: L :: BitVec.ofNat 256 (m + 1) :: T, s) =
      some (.inr (L.toNat, BitVec.ofNat 256 (t + (m + 1)) :: T, s)) := by
  have h1 := add_ofNat (m + 1) t
  have h2 := add_ofNat t (m + 1)
  have h3 := lt_add_ofNat t (m + 1) ht
  have h4 := lt_add_ofNat (m + 1) t (by omega)
  have hlt : (BitVec.ofNat 256 (m + 1 + t) < BitVec.ofNat 256 (m + 1)) = False := by
    simp only [eq_iff_iff, iff_false, BitVec.lt_def, BitVec.toNat_ofNat]; omega
  evm_run
  all_goals (try rw [Nat.add_comm (m + 1) t])
  all_goals (try rfl)

section entry
variable (o : Oracle) (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64)
include hv hsel in
theorem c1 (s : State) (rest : List EVM.Program.Instr) :
    EVM.Program.exec o call 0 (.effect .callvalue 0 :: .jumpi 2 :: .op (.stack (.push 0)) :: .effect .calldataload 1 ::
      .op (.stack (.push 224)) :: .op (.stack .shr) :: .op (.stack (.dup 0)) :: .op (.stack (.push 0xb119ebfe)) ::
      .op (.stack .sub) :: .jumpi 2 :: rest) [] s =
    EVM.Program.exec o call 0 rest [2971266046] s := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | sym_mem)

theorem c2 (s : State) (rest : List EVM.Program.Instr) :
    EVM.Program.exec o call 0 (.op (.stack (.push 128)) :: .op (.stack (.push 64)) :: .op .store :: rest)
      [2971266046] s =
    EVM.Program.exec o call 0 rest [2971266046] { s with memory := s.memory.store 64 128 } := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | sym_mem)

include hsz hn in
theorem c3 (s : State) (rest : List EVM.Program.Instr) :
    EVM.Program.exec o call 0 (.op (.stack (.push 36)) :: .op (.stack .calldatasize) :: .op (.stack .lt) ::
      .op (.stack (.push 64)) :: .op (.stack (.push 4)) :: .effect .calldataload 1 :: .op (.stack .gt) ::
      .op (.stack .or) :: .jumpi 2 :: rest) [2971266046] s =
    EVM.Program.exec o call 0 rest [2971266046] s := by
  have hg : ¬ (64 : EvmRules.Word) < calldataWord call 4 := by
    simp only [BitVec.lt_def]; simp; omega
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | sym_mem)

theorem c4 (s : State) (rest : List EVM.Program.Instr) :
    EVM.Program.exec o call 0 (.op (.stack (.push 4)) :: .effect .calldataload 1 :: .pushLabel 3 :: .jump 1 :: rest)
      [2971266046] s =
    .inr (1, [3#256, calldataWord call 4, 2971266046], s) := by
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  repeat (first | sym_eval | sym_cond | sym_mem)
  all_goals (try subst hcd)
  all_goals (try rfl)

include hv hsel hsz hn in
/-- Block 0: the dispatcher checks the value, the selector, the size and @@n ≤ 64@@, stores the free
memory pointer and calls the function at @@n@@ with return label 3. -/
theorem entry_step :
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) 1 (0, [], State.initial call) =
      some (.inr (1, [3#256, calldataWord call 4, 2971266046],
        { State.initial call with memory := (State.initial call).memory.store 64 128 })) := by
  simp only [SolarTV.CutPoint.steps, EVM.Program.block, evm6, List.getElem?_cons_zero]
  rw [c1 o call hv hsel, c2 o call, c3 o call hsz hn, c4 o call]

end entry

/-- Block 3: the dispatcher returns the function's result word. -/
theorem exit_step (o : Oracle) (call : Call) (r : EvmRules.Word) (T : EVM.Stack) (s : State)
    (hT : T.length ≤ 900) :
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) 1 (3, r :: T, s) =
      some (.inl (Halt.ret (Mem.wordBytes r), { s with memory := s.memory.store 0 r })) := by
  evm_run
  all_goals (try rfl)

/-- **The recursive function's block count, by its measure**: from its entry at measure `v ≤ 64`,
under any return label `L` and any stack `T` below, the final EVM IR returns `tri v` to `L` in
exactly `2 * v + 2` blocks. -/
theorem fn_steps (o : Oracle) (call : Call) : ∀ v, v ≤ 64 → ∀ (L : EvmRules.Word) (T : EVM.Stack) (s : State),
    T.length + 2 * v ≤ 900 →
    SolarTV.CutPoint.steps (EVM.Program.block o call evm6) (2 * v + 2) (1, L :: BitVec.ofNat 256 v :: T, s) =
      some (.inr (L.toNat, BitVec.ofNat 256 (SolarTV.Milestone.RecSum.tri v) :: T, s))
  | 0, _, L, T, s, hT => fn_zero o call L T s (by omega)
  | m + 1, hv, L, T, s, hT => by
    have h1 := fn_call o call L T s m hv (by omega)
    have ih := fn_steps o call m (by omega) (BitVec.ofNat 256 4) (L :: BitVec.ofNat 256 (m + 1) :: T) s
      (by simp only [List.length_cons]; omega)
    have h4 : (BitVec.ofNat 256 4 : EvmRules.Word).toNat = 4 := rfl
    rw [h4] at ih
    have htm := SolarTV.Milestone.RecSum.tri_le m (by omega)
    have h3 := fn_resume o call L T s m (SolarTV.Milestone.RecSum.tri m) (by omega) (by omega)
    rw [show 2 * (m + 1) + 2 = 1 + ((2 * m + 2) + 1) by omega, SolarTV.CutPoint.steps_add 1 _ _ _ h1,
      SolarTV.CutPoint.steps_add (2 * m + 2) 1 _ _ ih, h3, SolarTV.Milestone.RecSum.tri_succ]

/-- **A call of `total(n)`, `n ≤ 64`, ends within `2 * n + 4` blocks of the final EVM IR.** -/
theorem ends_within (o : Oracle) (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64) :
    ∃ r, Machine.iterate (EVM.Program.block o call evm6) (2 * (calldataWord call 4).toNat + 4)
      (0, [], State.initial call) = some r := by
  set a := (calldataWord call 4).toNat with ha
  have h0 := entry_step o call hv hsel hsz hn
  have hw : BitVec.ofNat 256 a = calldataWord call 4 := by rw [ha]; exact BitVec.ofNat_toNat _ _ ▸ by simp
  have hf := fn_steps o call a hn (3#256) [2971266046]
    { State.initial call with memory := (State.initial call).memory.store 64 128 } (by simp; omega)
  rw [hw] at hf
  have h3 : ((3#256 : EvmRules.Word)).toNat = 3 := rfl
  rw [h3] at hf
  have hx := exit_step o call (BitVec.ofNat 256 (SolarTV.Milestone.RecSum.tri a)) [2971266046]
    { State.initial call with memory := (State.initial call).memory.store 64 128 } (by simp)
  have hall : ∃ X, SolarTV.CutPoint.steps (EVM.Program.block o call evm6) (2 * a + 4)
      (0, [], State.initial call) = some (.inl X) := ⟨_, by
    rw [show 2 * a + 4 = 1 + ((2 * a + 2) + 1) by omega, SolarTV.CutPoint.steps_add 1 _ _ _ h0,
      SolarTV.CutPoint.steps_add (2 * a + 2) 1 _ _ hf]
    exact hx⟩
  obtain ⟨X, hX⟩ := hall
  exact ⟨X, by rw [SolarTV.CutPoint.iterate_eq]; exact SolarTV.CutPoint.run_of_steps hX⟩

/-- The assembly checker's gas bound for RecSum's certificate: `22100 * (n * 28) + memoryGasCost 96`. -/
theorem gasBound_eq (n : Nat) :
    SolidCore.Refinement.Solar.AssembleLoop.gasBoundL SolarTV.Milestone.RecSum.cert n = 618800 * n + 9 := by
  have hb : SolidCore.Refinement.Solar.AssembleLoop.bmax SolarTV.Milestone.RecSum.cert = 28 := by decide
  have hm : EthLib.Execution.Evm.memoryGasCost SolarTV.Milestone.RecSum.cert.top = 9 := by decide
  unfold SolidCore.Refinement.Solar.AssembleLoop.gasBoundL
  rw [hb, hm]; omega

/-- **`total(n)` on the exact bytecode at a concrete gas**: on a call with no value, `total`'s
selector, a full argument word and `n ≤ 64`, the runtime bytecode solar emits for RecSum.sol succeeds,
returning the 32 bytes of `n * (n + 1) / 2`, at every gas from `618800 * (2 * n + 4) + 9` on. -/
theorem bytecode_gas (call : Call)
    (hv : BitVec.ofNat 256 call.callvalue = 0)
    (hsel : EvmRules.Evm.shr 224 (calldataWord call 0) = 2971266046)
    (hsz : ¬ BitVec.ofNat 256 call.calldata.size < 36)
    (hn : (calldataWord call 4).toNat ≤ 64) :
    ∀ gas, 618800 * (2 * (calldataWord call 4).toNat + 4) + 9 ≤ gas → ∃ obs,
      SolidCore.Refinement.Final.Target.runWith gas SolarTV.Milestone.RecSum.code call = some obs ∧
      obs.success = true ∧
      obs.output = (Mem.wordBytes (BitVec.ofNat 256 (SolarTV.Milestone.RecSum.tri (calldataWord call 4).toNat))).map
        BitVec.toNat := by
  obtain ⟨r, hit⟩ := ends_within SolarTV.Milestone.RecSum.oracle0 call hv hsel hsz hn
  have hf : ∀ gas, 618800 * (2 * (calldataWord call 4).toNat + 4) + 9 ≤ gas →
      SolidCore.Refinement.Final.Target.runWith gas SolarTV.Milestone.RecSum.code call =
        some (Machine.observe call r.2 r.1) := fun gas hg =>
    SolidCore.Refinement.Solar.AssembleRec.forward_of_checkF SolarTV.Milestone.RecSum.check_ok
      SolarTV.Milestone.RecSum.oracle0 (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) call
      (SolarTV.Milestone.RecSum.heads_ok _ call) _ r hit (by rw [gasBound_eq]; exact hg)
  obtain ⟨G, hG⟩ := SolarTV.Milestone.RecSum.total_returns_bytecode call hv hsel hsz hn
  intro gas hgas
  obtain ⟨obs', h1, h2, h3⟩ := hG (max gas G) (Nat.le_max_right _ _)
  rw [hf (max gas G) (Nat.le_trans hgas (Nat.le_max_left _ _))] at h1
  obtain rfl := Option.some.inj h1
  exact ⟨_, hf gas hgas, h2, h3⟩

/-- info: 'Verify.Phase3.RecSource.Gas.bytecode_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytecode_gas

/-! ## From the source, at a concrete gas -/

open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop
open Verify.Phase3.RecSource (runtime_is_fresh contract_ok source_returns wordBytes_out totalSel fuel wordOut
  runtimeBytes contract? wordSize_gt)

/-- **RecSum from its source to its bytecode, at a concrete gas.** For every storage `σ` and `a ≤ 64`,
on the call of `total(a)` with no value: SolidCore's run of the checked source succeeds, returning
`a * (a + 1) / 2`, and at every gas from `618800 * (2 * a + 4) + 9` on the runtime bytecode solar
emits for RecSum.sol (bound to this run's fresh compile by the first conjunct) succeeds with the same
output. -/
theorem source_to_bytecode_gas :
    SolarTV.Export.RecSum.bytecode = runtimeBytes ∧
    ∃ c, contract? = .ok c ∧ ∀ (σ : List (Nat × Nat)) (a : Nat), a ≤ 64 →
      ∃ obs, runtimeRun fuel c { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } =
        some obs ∧ obs.success = true ∧ obs.output = wordOut (a * (a + 1) / 2) ∧
        ∀ gas, 618800 * (2 * a + 4) + 9 ≤ gas → ∃ obs',
          SolidCore.Refinement.Final.Target.runWith gas SolarTV.Milestone.RecSum.code
            { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } = some obs' ∧
          obs'.success = true ∧ obs'.output = obs.output := by
  refine ⟨runtime_is_fresh, ?_⟩
  obtain ⟨c, hc⟩ := contract_ok
  refine ⟨c, hc, fun σ a ha => ?_⟩
  have haW : a < 2 ^ 256 := by omega
  obtain ⟨obs, hrun, hs, ho, -⟩ := source_returns hc σ a haW
  refine ⟨obs, hrun, hs.mpr ha, ho ha, ?_⟩
  have hf := callFacts totalSel (by decide) [a] (by simpa using haW) σ
  have h4 : (SolarTV.Machine.calldataWord
      { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } 4).toNat = a := by
    have := hf.args 0 (by simp) (by have := wordSize_gt; omega)
    simpa [WExpr.eval, Nat.mod_eq_of_lt haW] using this
  have hG := bytecode_gas { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ }
    (by simp [hf.value]) (by rw [hf.selector]; rfl)
    (by rw [hf.size]; simp only [List.length_singleton]; decide) (by rw [h4]; exact ha)
  intro gas hg
  rw [h4] at hG
  obtain ⟨obs', h1, h2, h3⟩ := hG gas hg
  refine ⟨obs', h1, h2, ?_⟩
  rw [h3, ho ha]
  exact wordBytes_out (Verify.Phase3.RecSource.tri a) (by have := Verify.Phase3.RecSource.tri_le a ha; omega)

/-- One bound for every argument: 81681609 gas (`618800 * 132 + 9`) suffices for every `a ≤ 64`. -/
theorem uniform_gas (a gas : Nat) (ha : a ≤ 64) (hg : 81681609 ≤ gas) : 618800 * (2 * a + 4) + 9 ≤ gas := by
  omega

/-- info: 'Verify.Phase3.RecSource.Gas.source_to_bytecode_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_to_bytecode_gas

end Verify.Phase3.RecSource.Gas
