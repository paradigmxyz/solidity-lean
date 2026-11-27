import Verify.Phase3.RecSource.Gas
import Verify.Phase3.RecSource.CertSpec
import SolidCore.Refinement.Solar.AssembleRecWithin
import Verify.Shapes

/-!
# RecSum: the published shape, from the source to the exact bytecode

`Shapes.Certified` for RecSum's `total` on every call `total(a)` with `a ≤ 64`, no value and any
storage (`Valid`, the domain of its `@custom:succeeds-if msg.value == 0 && n <= 64`):

* **equivalence at every gas** (`equiv`): every result the bytecode gives at any gas is the source's,
  or a failure that changes nothing. The backward assembly theorem with frames
  (`AssembleRec.within_of_checkF`) carries it to the final EVM IR's result, which is the source's
  (`evm_obs`, `source_obs`);
* **termination** with success, and the **postcondition**: the output is the word
  `a * (a + 1) / 2`, `total`'s `@custom:ensures n <= 64 ==> result == n * (n + 1) / 2`;
* **resources** at the explicit bound `G call = 618800 * (2 * a + 4) + 9` (at most 81681609 for
  every `a ≤ 64`, below `2 ^ 64`): the assembly checker's bound `gasBoundL cert n` for the
  final EVM IR's block count, `n = 2 * a + 4` by `sum`'s measure (`Gas.ends_within`).

The source semantics is SolidCore's runtime (`solidCoreRuntime fuel`) of the type checker's
contract of RecSum.sol (`contract?`, bound to the front end's AST by rec_source.py); the
recursion runs through SolidCore's own internal calls, by induction on the measure
(`Runs.sum_runs`). The postcondition is a Lean predicate written for `total`'s ensures, not
solar-verify's export.
-/

namespace Verify.Phase3.RecSource.Cert

open SolarTV SolarTV.Machine SolarTV.Export.RecSum
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop
open Verify.Phase3.RecSource (runtime_is_fresh contract_ok source_returns runs wordBytes_out totalSel fuel
  wordOut runtimeBytes contract? wordSize_gt totalTree le64)

theorem word_arg (a : Nat) (σ : List (Nat × Nat)) (ha : a < 2 ^ 256) :
    (calldataWord (totalCall a σ) 4).toNat = a ∧ BitVec.ofNat 256 (totalCall a σ).callvalue = 0 ∧
      EvmRules.Evm.shr 224 (calldataWord (totalCall a σ) 0) = 2971266046 ∧
      ¬ BitVec.ofNat 256 (totalCall a σ).calldata.size < 36 := by
  have hf := callFacts totalSel (by decide) [a] (by simpa using ha) σ
  refine ⟨?_, by simp [totalCall, hf.value], by unfold totalCall; rw [hf.selector]; rfl,
    by unfold totalCall; rw [hf.size]; simp only [List.length_singleton]; decide⟩
  have := hf.args 0 (by simp) (by have := wordSize_gt; omega)
  simpa [totalCall, WExpr.eval, Nat.mod_eq_of_lt ha] using this

/-- **The source's result**: SolidCore's run of `total(a)`, `a ≤ 64`, is `result a σ`. -/
theorem source_obs {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (a : Nat) (σ : List (Nat × Nat)) (ha : a ≤ 64) :
    runtimeRun fuel c (totalCall a σ) = some (result a σ) := by
  have haW : a < 2 ^ 256 := by omega
  obtain ⟨obs, hrun, hs, ho, -⟩ := source_returns hc σ a haW
  have h2 := runs hc σ a haW
  rw [hrun] at h2
  have hobs := Option.some.inj h2
  have hl : obs.logs = [] ∧ obs.storage = slotValue σ := by
    rw [hobs]
    simp only [totalTree, Tree.eval]
    split <;> exact ⟨rfl, rfl⟩
  unfold totalCall
  rw [hrun]
  obtain ⟨s, o, l, st⟩ := obs
  simp only at hs ho hl
  obtain ⟨rfl, rfl⟩ := hl
  rw [hs.mpr ha, ho ha]
  rfl

theorem storageOf_initial (call : Call) : storageOf (State.initial call) = slotValue call.storage := by
  funext slot
  simp only [storageOf, State.initial, BitVec.toNat_ofNat]
  rw [SolidCore.Refinement.Evm.Wide.slotValue_mod,
    Nat.mod_eq_of_lt (SolidCore.Refinement.Evm.Wide.slotValue_lt _ _)]

/-- **The final EVM IR's result**: on `total(a)`, `a ≤ 64`, it is `result a σ`, read off the
backend stages' simulation of `Spec.total_returns`. -/
theorem evm_obs (a : Nat) (σ : List (Nat × Nat)) (ha : a ≤ 64) :
    (evmirSem SolarTV.Milestone.RecSum.oracle0).run evm6 (totalCall a σ) = some (result a σ) := by
  have haW : a < 2 ^ 256 := by omega
  obtain ⟨h4, hv, hsel, hsz⟩ := word_arg a σ haW
  have hends := SolarTV.Milestone.RecSum.total_returns SolarTV.Milestone.RecSum.oracle0 (totalCall a σ) hv hsel hsz (by rw [h4]; exact ha)
  obtain ⟨r', ⟨n, hn⟩, hag⟩ := SolarTV.Milestone.RecSum.recsum_certified SolarTV.Milestone.RecSum.oracle0 (totalCall a σ) trivial _ hends
  have hres : (evmirSem SolarTV.Milestone.RecSum.oracle0).run evm6 (totalCall a σ) =
      some (observe (totalCall a σ) r'.2 r'.1) := by
    change (EVM.Program.layer.result SolarTV.Milestone.RecSum.oracle0 evm6 (totalCall a σ)).map _ = _
    rw [EVM.Program.layer.result_of_ends ⟨n, hn⟩]
    rfl
  rw [hres, h4] at *
  obtain ⟨h', s'⟩ := r'
  cases h' with
  | ret e =>
    simp only [Agree] at hag
    obtain ⟨rfl, hst, -, hw⟩ := hag
    simp only [observe, result, Option.some.injEq, Observable.mk.injEq, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [wordBytes_out _ (by have := SolarTV.Milestone.RecSum.tri_le a ha; omega)]
      rfl
    · simp only [logs, ← hw]
      rfl
    · rw [storageOf_congr hst.symm]
      exact storageOf_initial _
  | stop =>
    simp only [Agree] at hag
    exact absurd hag.1 (by simp [Mem.wordBytes])
  | revert e => simp [Agree] at hag
  | invalid => simp [Agree] at hag

set_option maxRecDepth 100000 in
/-- **RecSum, certified**: the published shape for `total` on the exact runtime bytecode. -/
theorem certified {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Certified (solidCoreRuntime fuel) c SolarTV.Milestone.RecSum.code Valid Allowed Post gas := by
  refine ⟨⟨totalCall 0 [], 0, [], by decide, rfl⟩, ?_, ?_, ?_, ?_⟩
  · -- Equivalence at every gas: the backward assembly theorem with frames.
    intro g _ call hcall obs hrun
    obtain ⟨a, σ, ha, rfl⟩ := hcall
    have W := SolidCore.Refinement.Solar.AssembleRec.within_of_checkF SolarTV.Milestone.RecSum.check_ok SolarTV.Milestone.RecSum.oracle0
      (fun h => absurd h (by decide)) Valid (fun call _ => SolarTV.Milestone.RecSum.heads_ok SolarTV.Milestone.RecSum.oracle0 call) g
    rcases W (totalCall a σ) ⟨a, σ, ha, rfl⟩ obs hrun with e | e
    · left
      show runtimeRun fuel c (totalCall a σ) = some obs
      rw [source_obs hc a σ ha, ← evm_obs a σ ha]
      exact e
    · exact Or.inr e
  · intro call hcall
    obtain ⟨a, σ, ha, rfl⟩ := hcall
    exact ⟨_, source_obs hc a σ ha, rfl⟩
  · intro call hcall obs hs a' σ' he ha'
    obtain ⟨a, σ, ha, rfl⟩ := hcall
    have hs' : runtimeRun fuel c (totalCall a σ) = some obs := hs
    rw [source_obs hc a σ ha] at hs'
    obtain rfl := Option.some.inj hs'
    have h1 := (word_arg a σ (by omega)).1
    rw [he, (word_arg a' σ' (by omega)).1] at h1
    subst h1
    rfl
  · intro call hcall
    obtain ⟨a, σ, ha, rfl⟩ := hcall
    obtain ⟨h4, hv, hsel, hsz⟩ := word_arg a σ (by omega)
    refine ⟨by unfold gas; rw [h4]; omega, fun g hg _ => ?_⟩
    obtain ⟨r, hit⟩ := Gas.ends_within SolarTV.Milestone.RecSum.oracle0 (totalCall a σ) hv hsel hsz (by rw [h4]; exact ha)
    generalize hN : 2 * (calldataWord (totalCall a σ) 4).toNat + 4 = N at hit
    have hf := SolidCore.Refinement.Solar.AssembleRec.forward_of_checkF SolarTV.Milestone.RecSum.check_ok SolarTV.Milestone.RecSum.oracle0
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (totalCall a σ)
      (SolarTV.Milestone.RecSum.heads_ok _ _) N r hit (gas := g)
      (by rw [Gas.gasBound_eq, ← hN]; exact hg)
    have hres : (evmirSem SolarTV.Milestone.RecSum.oracle0).run evm6 (totalCall a σ) =
        some (observe (totalCall a σ) r.2 r.1) := by
      change (EVM.Program.layer.result SolarTV.Milestone.RecSum.oracle0 evm6 (totalCall a σ)).map _ = _
      rw [EVM.Program.layer.result_of_ends ⟨N, hit⟩]
      rfl
    show _ = runtimeRun fuel c (totalCall a σ)
    rw [hf, source_obs hc a σ ha, ← evm_obs a σ ha, hres]

/-- The term the published statement's proof is (tools/certify/rec_final.py's shape.json): the checked
source and its certificate on the exact bytecode. -/
theorem shape_ok : ∃ c, contract? = .ok c ∧
    Shapes.Certified (solidCoreRuntime fuel) c SolarTV.Milestone.RecSum.code Valid Allowed Post gas := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨c, hc, certified hc⟩

/-- **The published statement's content**: the bytes are this run's fresh compile, and RecSum is
certified on them. -/
theorem published :
    SolarTV.Export.RecSum.bytecode = runtimeBytes ∧
    ∃ c, contract? = .ok c ∧ Shapes.Certified (solidCoreRuntime fuel) c SolarTV.Milestone.RecSum.code Valid Allowed Post gas := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨runtime_is_fresh, c, hc, certified hc⟩

/-- The bound is concrete: 81681609 gas for every valid call. -/
theorem gas_le (call : Call) (h : Valid call) : gas call ≤ 81681609 := by
  obtain ⟨a, σ, ha, rfl⟩ := h
  unfold gas
  rw [(word_arg a σ (by omega)).1]
  omega

/-- info: 'Verify.Phase3.RecSource.Cert.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms published

end Verify.Phase3.RecSource.Cert
