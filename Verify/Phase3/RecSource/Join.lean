import Verify.Phase3.RecSource.Total
import SolidCore.Refinement.Generic.Stage
import Verify.Phase3.RecSum.Bytecode

/-!
# RecSum from its source to its bytecode

The property solar-verify proves of `RecSum.total` (`n <= 64 ==> result == n * (n + 1) / 2`, with
`sum`'s contract inferred and proved by induction on its measure) holds of the Solidity source in
SolidCore's runtime semantics (`source_returns`, through `total_runs` and `sum_runs`: induction on
`sum`'s measure in SolidCore's own interpreter), and the exact bytecode solar emits returns the same
output on the same calls (`total_returns_bytecode`, the MIR-to-bytecode theorem, whose
MIR-level property is now the source's: `source_to_bytecode`). `runtimeBytes` is this run's fresh
compile of RecSum.sol (`-Ogas --evm-version osaka`); `runtime_is_fresh` binds the proof's bytecode to it.

What this does not state: the backward simulation (a bytecode run at any gas is the source's or
inert) and an explicit gas bound, which the published shapes (`Shapes.Certified`) need; the gas
bound here is existential, from the assembly checker's bound on the run's blocks.
-/

namespace Verify.Phase3.RecSource
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- The statement's fuel: past `16 * 65 + 5`, what `total` with `n ≤ 64` needs. -/
def fuel : Nat := 2000

/-- The runtime bytecode a fresh compile of RecSum.sol gives. -/
def runtimeBytes : List Nat :=
  [0x34, 0x60, 0x3a, 0x57, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0xb1, 0x19, 0xeb, 0xfe, 0x03, 
    0x60, 0x3a, 0x57, 0x60, 0x80, 0x60, 0x40, 0x52, 0x60, 0x24, 0x36, 0x10, 0x60, 0x40, 0x60, 0x04, 
    0x35, 0x11, 0x17, 0x60, 0x3a, 0x57, 0x60, 0x04, 0x35, 0x60, 0x3e, 0x5b, 0x81, 0x15, 0x60, 0x4f, 
    0x57, 0x60, 0x01, 0x82, 0x03, 0x60, 0x45, 0x60, 0x2b, 0x56, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x5f, 
    0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x82, 0x01, 0x91, 0x82, 0x10, 0x60, 0x55, 0x57, 0x56, 0x5b, 
    0x90, 0x50, 0x5f, 0x90, 0x56, 0x5b, 0x60, 0x11, 0x60, 0x20, 0x52, 0x63, 0x4e, 0x48, 0x7b, 0x71, 
    0x5f, 0x52, 0x60, 0x24, 0x60, 0x1c, 0xfd]

set_option maxRecDepth 100000 in
theorem runtime_is_fresh : SolarTV.Export.RecSum.bytecode = runtimeBytes :=
  @of_decide_eq_true _ (instDecidableEqList _ _) (by decide +kernel)

theorem envOf_eq {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hf : c.core.storageFields = [])
    (he : c.core.eventDecls = []) :
    ({ envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } : EraseEnv) = envT c.core.table := by
  simp only [envOf, envT, hf, he]

/-- `total`'s tree: empty revert above 64, else the 32 bytes of `n * (n + 1) / 2`. -/
def totalTree : Tree := .ite le64 (.halt true (wordOBytes triW) [] []) (.halt false [] [] [])

theorem tree_eq : brTree totalFn (argFacts [2 ^ 256 - 1] 0) totalBr = some totalTree := rfl

/-- **Every call of `total(a)` with no value runs, in SolidCore, to its tree's observable.** -/
theorem runs {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) :
    runtimeRun fuel c { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } =
      some (totalTree.eval ⟨[a], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩).obs := by
  obtain ⟨hf, hev, hfind, htbl⟩ := shape_of hc
  have hw : widthsOf totalFn.params totalFn.paramAbiCleanups = some [2 ^ 256 - 1] := rfl
  have hargs : ∀ x ∈ [a], x < 2 ^ 256 := by simpa using ha
  have hclean : argsClean [2 ^ 256 - 1] [a] = true := by
    show (decide (a < 2 ^ 256) && true) = true
    simp only [Bool.and_true, decide_eq_true_eq]
    exact ha
  have hdec := decode_args hw [a] rfl hargs
  rw [if_pos hclean] at hdec
  have hb : BodyRuns { envOf c.core with facts := argFacts [2 ^ 256 - 1] 0 } fuel totalFn totalBr := by
    rw [envOf_eq hf hev]
    exact total_runs htbl fuel (by unfold fuel; omega)
  exact runtime_run_clean (by decide) hfind hw rfl hb tree_eq [a] rfl hargs hclean hdec

/-- The 32 big-endian bytes of `x`. -/
def wordOut (x : Nat) : List Nat := (List.range 32).map fun i => x / 256 ^ (31 - i) % 256

/-- **total's property in the source**: `total(a)` with `a ≤ 64` succeeds, returning the word
`a * (a + 1) / 2`; with `a > 64` it reverts with empty data and keeps the storage. -/
theorem source_returns {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) :
    ∃ obs, runtimeRun fuel c { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } =
      some obs ∧ (obs.success = true ↔ a ≤ 64) ∧ (a ≤ 64 → obs.output = wordOut (tri a)) ∧
      (64 < a → obs.output = [] ∧ obs.storage = slotValue σ) := by
  refine ⟨_, runs hc σ a ha, ?_⟩
  set ρ : Val := ⟨[a], slotValue σ, solHash, SolidCore.Refinement.Generic.callerWord⟩ with hρ
  have hW := wordSize_gt
  have ha0 : (WExpr.arg 0).eval ρ = a := by
    simp only [WExpr.eval, hρ, List.getD_cons_zero]; exact Nat.mod_eq_of_lt ha
  have hle : le64.eval ρ = if a ≤ 64 then 1 else 0 := by
    have e : le64.eval ρ = UnOp.iszero.eval (BinOp.gt.eval ((WExpr.arg 0).eval ρ)
        (64 % Generic.wordSize) % Generic.wordSize) % Generic.wordSize := rfl
    rw [e, ha0, Nat.mod_eq_of_lt (show 64 < Generic.wordSize by omega)]
    by_cases h : a ≤ 64
    · simp [UnOp.eval, BinOp.eval, h, show ¬ 64 < a by omega]
    · simp [UnOp.eval, BinOp.eval, h, show 64 < a by omega]
  by_cases h : a ≤ 64
  · have hev : totalTree.eval ρ = (Tree.halt true (wordOBytes triW) [] []).eval ρ := by
      simp [totalTree, Tree.eval, hle, h]
    have ht : triW.eval ρ = tri a := by rw [triW_eval (by rw [ha0]; exact h), ha0]
    refine ⟨?_, fun _ => ?_, fun h' => absurd h' (by omega)⟩
    · simp [Res.obs, hev, Tree.eval, h]
    · simp only [Res.obs, hev, Tree.eval, wordOBytes, wordOut, List.map_map]
      apply List.map_congr_left
      intro i _
      simp [OByte.eval, ht]
  · have hev : totalTree.eval ρ = (Tree.halt false [] [] []).eval ρ := by
      simp [totalTree, Tree.eval, hle, h]
    refine ⟨?_, fun h' => absurd h' h, fun _ => ?_⟩
    · simp [Res.obs, hev, Tree.eval, h]
    · simp only [Res.obs]
      rw [hev]
      exact ⟨rfl, rfl⟩

theorem wordBytes_out (x : Nat) (hx : x < 2 ^ 256) :
    (SolarTV.Machine.Mem.wordBytes (BitVec.ofNat 256 x)).map BitVec.toNat = wordOut x := by
  simp only [SolarTV.Machine.Mem.wordBytes, wordOut, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp, SolarTV.Memory.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * (31 - i)) = 256 ^ (31 - i) by rw [pow_mul]; norm_num, show 2 ^ 8 = 256 by norm_num]

/-- **RecSum from its source to its bytecode.** For every storage `σ` and `a ≤ 64`, on the call of
`total(a)` with no value: SolidCore's run of the checked source succeeds, returning `a * (a + 1) / 2`
(the ensures of `total`), and from some gas on the runtime bytecode solar emits for RecSum.sol (the
proof's `code`, whose bytes are this run's fresh compile, `runtime_is_fresh`) succeeds with the same
output. -/
theorem source_to_bytecode :
    SolarTV.Export.RecSum.bytecode = runtimeBytes ∧
    ∃ c, contract? = .ok c ∧ ∀ (σ : List (Nat × Nat)) (a : Nat), a ≤ 64 →
      ∃ obs, runtimeRun fuel c { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ } =
        some obs ∧ obs.success = true ∧ obs.output = wordOut (a * (a + 1) / 2) ∧
        ∃ G, ∀ gas, G ≤ gas → ∃ obs',
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
  obtain ⟨G, hG⟩ := SolarTV.Milestone.RecSum.total_returns_bytecode
    { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ }
    (by simp [hf.value]) (by rw [hf.selector]; rfl)
    (by rw [hf.size]; simp only [List.length_singleton]; decide) (by rw [h4]; exact ha)
  refine ⟨G, fun gas hg => ?_⟩
  obtain ⟨obs', h1, h2, h3⟩ := hG gas hg
  refine ⟨obs', h1, h2, ?_⟩
  rw [h3, h4, ho ha]
  exact wordBytes_out (tri a) (by have := tri_le a ha; omega)

/-- The property is not vacuous, and not any other: at `total(2)` the source returns 3, so a claim of
`a * a` (4) is refuted in the kernel. -/
example {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) (σ : List (Nat × Nat)) :
    ¬ ∀ obs, runtimeRun fuel c { calldata := Abi.calldata totalSel [2], callvalue := 0, storage := σ } =
      some obs → obs.output = wordOut (2 * 2) := by
  intro h
  obtain ⟨obs, hrun, -, ho, -⟩ := source_returns hc σ 2 (by decide)
  have := (ho (by decide)).symm.trans (h obs hrun)
  revert this
  decide

/-- A call above the bound reverts in the source: the ensures' `n <= 64` is the function's own
`require`, not an assumption of the statement. -/
example {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) (σ : List (Nat × Nat)) :
    ∃ obs, runtimeRun fuel c { calldata := Abi.calldata totalSel [65], callvalue := 0, storage := σ } =
      some obs ∧ obs.success = false := by
  obtain ⟨obs, hrun, hs, -, -⟩ := source_returns hc σ 65 (by decide)
  exact ⟨obs, hrun, by cases h : obs.success <;> simp_all⟩

/-- info: 'Verify.Phase3.RecSource.source_to_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_to_bytecode

end Verify.Phase3.RecSource
