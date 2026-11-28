import Verify.Partial.CounterAny

/-!
# Counter.bump from every caller: the runs alone, with no property

`counter_run_any` is translation preservation for `bump(a)` from every caller, proved without any
specification. Its statement is `Verify.Partial.CounterAny.counter_partial_any` without the two
conjuncts that name a property (`CounterCtx.allowed` and the hand-written
`Verify.LoopSource.MirLink.BumpPost`), and its proof is that theorem's proof without the two
branches that prove them. It reuses only run lemmas of that module: `src_run_rt` (SolidCore's
runtime code from caller `x` runs `bump(a)` to the tree's observable) and `ends_at` (the final EVM IR
ends within `N a` blocks), with the loop checker's backward (`within_of_checkXLFrom`) and forward
(`gasEdge_ofXL_at`) gas lemmas. `tree_post_at`, `BumpPost` and `allowed` are not in its proof.

* Every result of EthLib's run of the exact bytes from `ctx` is the source's result `obs`, or an
  inert failure below `G a` gas (`Shapes.Inert`: no success, storage and logs unchanged; this names
  the shape of the failure, not its cause).
* From `G a` gas (below `2 ^ 256`) the bytes' result is `obs`. The interval is empty when
  `G a ≥ 2 ^ 256` (as at `a = 2 ^ 255`, `Verify.Partial.CounterAny.control_empty`).
-/

namespace Verify.Phase2.CounterRun
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop SolidCore.Refinement.Solar Contracts.VerifyCounter.Source
open SolidCore.Verify.Generic
open Verify.LoopSource.Equiv.CounterLoad Verify.LoopSource.Equiv.CounterCtx
open Verify.Partial.CounterAny (src_run_rt ends_at)

/-- **Translation preservation of `bump(a)` from every caller, with no property.** -/
theorem counter_run_any :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a : Nat), a < 2 ^ 256 →
          let call := Verify.LoopSource.MirLink.bumpCall σ a
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
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
  refine ⟨_, hsrc, ?_, fun gas hg _ => fwd gas hg⟩
  intro gas obs' hobs
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

end Verify.Phase2.CounterRun

/-- info: 'Verify.Phase2.CounterRun.counter_run_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.Phase2.CounterRun.counter_run_any
