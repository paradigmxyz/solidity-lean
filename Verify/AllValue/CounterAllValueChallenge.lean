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

namespace Verify.AllValue.CounterAllValueChallenge

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
              SolidCore.Verify.Generic.runAt ctx gas code call = some obs) := sorry

end Verify.AllValue.CounterAllValueChallenge
