import Verify.AssembleLoop.StageFromAt
import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter.bump, runtime partial correctness from every caller

`counter_partial_any` is the statement pinned in Verify/Partial/CounterAnyChallenge.lean (restated
verbatim below as an `example`). It leaves `Expected`, `ResourcesAt`, `Valid` and the bounded total
`CounterCtx.counter_expected` (`K ≤ Kmax`) unchanged; it is a separate row. Its source side is the
runtime code alone (`Loop.solidCoreRuntimeFrom`); the deployed-source corollary is not here.

* `src_run_rt` (G3): SolidCore's runtime code from caller `x` runs `bump(a)` for every storage and
  every `a < 2 ^ 256` to the tree's observable at `x` (`runtime_run_clean_from`): no deployment, no
  cover premise.
* `ends_at`: the final EVM IR ends within `N a = 2 a + 5` blocks on `bump(a)`, for every `a` and
  every oracle (`CounterCtx.ends` at `K := a`). This is the EVM IR block-fuel bound only.
* `counter_partial_any`: one call and one source result across the three parts; the backward
  part is `within_of_checkXLFrom` (any gas), the forward part `gasEdge_ofXL_at` at `N a` (gas from
  `G a`). `counter_partial_admissible`: for `a ≤ Kmax`, `G a < 2 ^ 64`, so a source-equal bytecode
  result exists at a gas below `2 ^ 64`.
* Controls: `control_wide` and `control_empty` (part 3 is empty at `a = 2 ^ 255`), `control_live`
  (a source result that is not inert).
-/

namespace Verify.Partial.CounterAny
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterLoad Verify.LoopSource.Equiv.CounterCtx

/-- **G3: the runtime code from caller `x`**, for every storage and argument word. -/
theorem src_run_rt {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) (x : Nat) (hx : x < 2 ^ 160)
    (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) :
    runtimeRunFrom x fuel c (Verify.LoopSource.MirLink.bumpCall σ a) =
      some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a x)).obs := by
  have hw : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [256] := rfl
  have hargs : ∀ v ∈ [a], v < 2 ^ 256 := by simpa using ha
  have hclean : argsClean [256] [a] = true := by
    show (decide (a < 2 ^ 256) && true) = true
    simp only [Bool.and_true, decide_eq_true_eq]; exact ha
  have hdec := decode_args hw [a] rfl hargs
  rw [if_pos hclean] at hdec
  exact runtime_run_clean_from x hx (by decide) (shape_of hc).2.2 hw rfl (bodyRunsFrom hc) treeFrom [a] rfl
    hargs hclean hdec

/-- **The EVM IR block fuel**: `bump(a)` ends within `N a` blocks, for every `a` and oracle. -/
theorem ends_at (o : Oracle) (σ : List (Nat × Nat)) {a : Nat} (ha : a < 2 ^ 256) :
    ∃ r, EVM.Program.run o (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7)) (Verify.LoopSource.MirLink.bumpCall σ a) (N a) = some r :=
  ends (K := a) o ⟨σ, a, Nat.le_refl a, ha, rfl⟩

theorem counter_partial_any :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
          let call := Verify.LoopSource.MirLink.bumpCall σ a
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
            Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨
                (gas < Verify.LoopSource.Equiv.CounterCtx.G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, Verify.LoopSource.Equiv.CounterCtx.G a ≤ gas → gas < 2 ^ 256 →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc⟩ := contract_ok
  refine ⟨c, hc, fun ctx hctx σ a ha => ?_⟩
  dsimp only
  have hAB := Assemble.address_ne_self hctx.1 hctx.2
  set o := SolidCore.Refinement.Shapes.oracleFrom ctx.caller
  have hsrc := src_run_rt hc ctx.caller hctx.1 σ ha
  have hev : (evmirSem o).run (AssembleCtxGas.guard Verify.LoopSource.Equiv.From.CtxGas.F
      (AssembleCtx.norm SolarTV.Export.Counter.evm7)) (Verify.LoopSource.MirLink.bumpCall σ a) =
        some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a ctx.caller)).obs := by
    show (evmirSem o).run (AssembleCtxGas.guard [] _) _ = _
    rw [guard_nil, AssembleCtx.sem_norm]
    exact evmir_run o σ ha ctx.caller
  have fwd : ∀ gas, G a ≤ gas →
      runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) (Verify.LoopSource.MirLink.bumpCall σ a) =
        some (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf σ a ctx.caller)).obs := by
    intro gas hg
    obtain ⟨obs, h1, h2⟩ := SolidCore.Refinement.Shapes.gasEdge_ofXL_at
      (Valid := fun call => call = Verify.LoopSource.MirLink.bumpCall σ a) (fun _ => N a)
      Verify.LoopSource.Equiv.From.CtxGas.check_ok (by decide)
      (by rintro o' _ rfl; exact Option.isSome_iff_exists.mpr (ends_at o' σ ha))
      (fun o' call _ => by show _ = EVM.Program.run o' (AssembleCtxGas.guard [] _) call _; rw [guard_nil])
      ctx.caller hctx.1 hctx.2 o (SolidCore.Refinement.Shapes.oracleFrom_ok hctx.1) _ rfl gas hg
    rw [AssembleCtx.sem_norm, evmir_run o σ ha ctx.caller] at h1
    show Final.Target.runWithFrom ctx.caller gas Verify.LoopSource.Equiv.From.CtxGas.code _ = _
    rw [h2, ← Option.some.inj h1]
  refine ⟨_, hsrc, ?_, ?_, ?_, fun gas hg _ => fwd gas hg⟩
  · intro hs
    exact ⟨eval_store_of_fail _ _ hs, eval_logs_of_fail _ _ hs⟩
  · exact tree_post_at ctx.caller Verify.LoopSource.Equiv.CounterObl.tree σ ha
  · intro gas obs' hobs
    by_cases hg : G a ≤ gas
    · left
      rw [fwd gas hg] at hobs
      exact (Option.some.inj hobs).symm
    obtain ⟨r, hr⟩ := ends_at o σ ha
    rcases AssembleCtxGas.within_of_checkXLFrom Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller hAB o
      (fun h => absurd h (by decide)) (by decide) _ (N a) r hr gas obs' hobs with h | h
    · left
      have he := SolidCore.Refinement.Shapes.evmir_run_of_iterate hr
      rw [hev] at he
      rw [h]
      exact (Option.some.inj he).symm
    · right
      exact ⟨Nat.lt_of_not_le hg, h⟩

/-- The challenge statement, verbatim, is `counter_partial_any`. -/
example :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
          let call := Verify.LoopSource.MirLink.bumpCall σ a
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
            Verify.LoopSource.MirLink.BumpPost call obs ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨
                (gas < Verify.LoopSource.Equiv.CounterCtx.G a ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, Verify.LoopSource.Equiv.CounterCtx.G a ≤ gas → gas < 2 ^ 256 →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := counter_partial_any

/-- **The gas-admissible cohort**: for `a ≤ Kmax` a source-equal bytecode result exists below `2 ^ 64`. -/
theorem counter_partial_admissible {a : Nat} (hK : a ≤ Kmax) :
    ∃ c, contract? = .ok c ∧ ∀ ctx : Context, ctx.Ok → ∀ σ : List (Nat × Nat),
      ∃ obs, (solidCoreRuntimeFrom ctx.caller fuel).run c (Verify.LoopSource.MirLink.bumpCall σ a) = some obs ∧
        ∃ gas, gas < 2 ^ 64 ∧
          runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) (Verify.LoopSource.MirLink.bumpCall σ a) = some obs := by
  obtain ⟨c, hc, h⟩ := counter_partial_any
  refine ⟨c, hc, fun ctx hctx σ => ?_⟩
  have ha : a < 2 ^ 256 := by unfold Kmax at hK; omega
  obtain ⟨obs, h1, -, -, -, h5⟩ := h ctx hctx σ a ha
  exact ⟨obs, h1, G a, G_lt hK, h5 _ (Nat.le_refl _) (Nat.lt_trans (G_lt hK) (by decide))⟩

/-! ## Scope controls -/

/-- At `a = 2 ^ 255` the per-call bound is past `2 ^ 256`. -/
theorem control_wide : ¬ G (2 ^ 255) < 2 ^ 256 := by
  have hb : AssembleLoop.bmax Verify.LoopSource.Equiv.From.CtxGas.cx.base = 34 := by decide
  have hm : EthLib.Execution.Evm.memoryGasCost Verify.LoopSource.Equiv.From.CtxGas.cx.base.top = 12 := by decide
  rw [G_eq, hb, hm]
  decide

/-- So part 3 is empty at `a = 2 ^ 255`: no bytecode termination is claimed there. -/
theorem control_empty : ∀ gas, G (2 ^ 255) ≤ gas → ¬ gas < 2 ^ 256 :=
  fun _ h1 h2 => control_wide (Nat.lt_of_le_of_lt h1 h2)

/-- Not every argument word has its bound in range. -/
theorem control_not_all : ¬ ∀ a, a < 2 ^ 256 → G a < 2 ^ 256 :=
  fun h => control_wide (h _ (by decide))

/-- A source result that is not inert (part 1 is not satisfied by inert results alone). -/
theorem control_live : (Verify.LoopSource.Equiv.CounterObl.T.eval (ρOf [(1, 8)] 3 0)).obs.success = true := by
  decide +kernel

end Verify.Partial.CounterAny

set_option pp.explicit true in
#check @Verify.Partial.CounterAny.counter_partial_any

set_option pp.explicit true in
#check @Verify.Partial.CounterAny.counter_partial_admissible

/-- info: 'Verify.Partial.CounterAny.counter_partial_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterAny.counter_partial_any

/-- info: 'Verify.Partial.CounterAny.counter_partial_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterAny.counter_partial_admissible

/-- info: 'Verify.Partial.CounterAny.src_run_rt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterAny.src_run_rt

/-- info: 'Verify.Partial.CounterAny.ends_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Partial.CounterAny.ends_at

#print axioms Verify.Partial.CounterAny.control_wide
#print axioms Verify.Partial.CounterAny.control_live
