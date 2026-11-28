import Verify.LoopSource.Equiv.CounterCtx

/-!
# Counter.bump, runtime partial correctness from every caller: the challenge statement

The statement `counter_partial_any` is pinned here, alone, with no proof. The proof module
(Verify/Partial/CounterAny.lean) never imports this file; it restates the statement verbatim as an
`example` closed by its theorem. Nothing imports this file.

For the checked contract `c`, every context `ctx.Ok` (a caller below `2 ^ 160` but the contract), every
storage `σ` and every argument word `a < 2 ^ 256`, with one call `bumpCall σ a` (call value 0) and the
exact runtime bytes, one source result `obs` of SolidCore's runtime code from `ctx.caller` at the
source's fuel such that:

1. the source runs to `obs` (no source fuel exhaustion at that fuel), `obs` is allowed and meets
   `BumpPost`;
2. at every gas, every bytecode result is `obs`, or an inert failure (a failure that changes
   nothing: `Shapes.Inert`) at a gas below `G a`;
3. at every gas from `G a` on below `2 ^ 256`, the bytecode runs to `obs`.

The source side is SolidCore's runtime code alone (`Loop.solidCoreRuntimeFrom`), so this is
runtime partial correctness: the deployed source (`Source.semAt`) is not part of it.

`G a` is the per-call bound, unbounded in `a`. Part 2 holds at every `gas : Nat` (EthLib's
`Message.gas` and its meter are `Nat`). Part 3 is stated below `2 ^ 256` (the GAS opcode reads the
meter as `BitVec.ofNat 256`), so it says nothing where `G a ≥ 2 ^ 256` (such as `a = 2 ^ 255`): no
bytecode termination or no-out-of-gas is claimed for those `a`.
-/

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
  sorry
