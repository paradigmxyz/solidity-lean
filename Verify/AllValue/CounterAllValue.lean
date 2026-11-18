import Verify.Partial.CounterAny
import Verify.AllValue.CounterValue

/-!
# Counter.bump from every caller, storage, argument and call value (G2)

`counter_all_value`: one call `bumpCallV σ a v` and one source result across all parts, for every
`ctx.Ok`, every storage `σ`, every `a < 2 ^ 256` and every `v < 2 ^ 256`. Value 0 is
`Verify.Partial.CounterAny.counter_partial_any` (`bumpCallV σ a 0 = bumpCall σ a` by `rfl`);
a value other than 0 is `Verify.AllValue.CounterValue.counter_nonpayable`, plus
`within_of_checkXLFrom` on its two-block revert run below `G0`.

Part 4's second alternative is an *inert failure* (failure, storage unchanged, no logs), allowed
only on the bytecode side and only below the call's bound `Gv`; it is not claimed to be out of
gas. Part 5 is capped at `gas < 2 ^ 256`, and for `v = 0` and large `a` its antecedent is
empty (`G a ≥ 2 ^ 256`, see `CounterAny.control_empty`): no universal bytecode termination or
no-out-of-gas is stated. `Expected`, `ResourcesAt` and `Valid` are unchanged.
-/

namespace Verify.AllValue.CounterAllValue
open SolarTV SolarTV.Machine SolidCore.Refinement SolidCore.Refinement.Solar

theorem counter_all_value :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 →
          let call := Verify.AllValue.CounterValue.bumpCallV σ a v
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          let Gv := if v = 0 then Verify.LoopSource.Equiv.CounterCtx.G a else Verify.AllValue.CounterValue.G0
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            (v = 0 → Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
              Verify.LoopSource.MirLink.BumpPost call obs) ∧
            (v ≠ 0 → obs = SolidCore.Refinement.Abi.rejected σ) ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨ (gas < Gv ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, Gv ≤ gas → gas < 2 ^ 256 →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := by
  obtain ⟨c, hc, hpart⟩ := Verify.Partial.CounterAny.counter_partial_any
  refine ⟨c, hc, fun ctx hctx σ a v ha hv => ?_⟩
  dsimp only
  by_cases hv0 : v = 0
  · subst hv0
    obtain ⟨obs, h1, h2, h3, h4, h5⟩ := hpart ctx hctx σ a ha
    exact ⟨obs, h1, fun _ => ⟨h2, h3⟩, fun h => absurd rfl h, h4, h5⟩
  · obtain ⟨hsrc, hbytes⟩ := Verify.AllValue.CounterValue.counter_nonpayable c hc ctx hctx σ a v ha hv hv0
    refine ⟨_, hsrc, fun h => absurd h hv0, fun _ => rfl, ?_, ?_⟩
    · intro gas obs' hobs
      simp only [hv0, ite_false]
      by_cases hg : Verify.AllValue.CounterValue.G0 ≤ gas
      · left
        rw [hbytes gas hg] at hobs
        exact (Option.some.inj hobs).symm
      · have hbv : BitVec.ofNat 256 (Verify.AllValue.CounterValue.bumpCallV σ a v).callvalue ≠ 0 := by
          intro h
          have := congrArg BitVec.toNat h
          simp [Verify.AllValue.CounterValue.bumpCallV] at this
          exact hv0 (by omega)
        obtain ⟨s, hs⟩ := Verify.AllValue.CounterValue.hit_value
          (SolidCore.Refinement.Shapes.oracleFrom ctx.caller) _ hbv
        rcases AssembleCtxGas.within_of_checkXLFrom Verify.LoopSource.Equiv.From.CtxGas.check_ok ctx.caller
          (Assemble.address_ne_self hctx.1 hctx.2) _ (fun h => absurd h (by decide)) (by decide) _ 2 _ hs
          gas obs' hobs with h | h
        · left
          rw [h]
          rfl
        · exact Or.inr ⟨Nat.lt_of_not_le hg, h⟩
    · intro gas hg _
      simp only [hv0, ite_false] at hg
      exact hbytes gas hg

/-- The challenge statement, verbatim, is `counter_all_value`. -/
example :
    ∃ c, Contracts.VerifyCounter.Source.contract? = .ok c ∧
      ∀ ctx : SolidCore.Verify.Generic.Context, ctx.Ok →
        ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 →
          let call := Verify.AllValue.CounterValue.bumpCallV σ a v
          let code := SolidCore.Verify.Generic.runtimeCode SolarTV.Export.Counter.bytecode
          let Gv := if v = 0 then Verify.LoopSource.Equiv.CounterCtx.G a else Verify.AllValue.CounterValue.G0
          ∃ obs, (SolidCore.Refinement.Generic.Loop.solidCoreRuntimeFrom ctx.caller
              Contracts.VerifyCounter.Source.fuel).run c call = some obs ∧
            (v = 0 → Verify.LoopSource.Equiv.CounterCtx.allowed call obs ∧
              Verify.LoopSource.MirLink.BumpPost call obs) ∧
            (v ≠ 0 → obs = SolidCore.Refinement.Abi.rejected σ) ∧
            (∀ gas : Nat, ∀ obs', SolidCore.Verify.Generic.runAt ctx gas code call = some obs' →
              obs' = obs ∨ (gas < Gv ∧ SolidCore.Refinement.Shapes.Inert call obs')) ∧
            (∀ gas : Nat, Gv ≤ gas → gas < 2 ^ 256 →
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := counter_all_value

/-- info: 'Verify.AllValue.CounterAllValue.counter_all_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counter_all_value

end Verify.AllValue.CounterAllValue
