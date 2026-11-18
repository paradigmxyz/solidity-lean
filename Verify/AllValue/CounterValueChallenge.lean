import Verify.LoopSource.Equiv.Counter.Resources
import Verify.LoopSource.Equiv.From.CtxGas
import Verify.ShapeCtxGasFrom
import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Generic.LoopRun
import Verify.Generic.Expected
import Verify.LoopSource.MirLink.Statement
import Contracts.VerifyCounter.Source

/-!
# Challenge: Counter's non-payable revert from every caller, value and storage (R3)

The exact statement of `Verify.AllValue.CounterValue.counter_nonpayable`, stated apart from its
proof with `sorry`. No module imports this file; `CounterValue.lean` restates the same
`Statement` and checks `example : Statement := counter_nonpayable`.
-/
namespace Verify.AllValue.CounterValueChallenge
open SolarTV SolarTV.Machine SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Solar Contracts.VerifyCounter.Source SolidCore.Verify.Generic

/-- `bump(a)` with call value `v` from storage `σ`: `MirLink.bumpCall` with the value free. -/
def bumpCallV (σ : List (Nat × Nat)) (a v : Nat) : Call :=
  { calldata := Abi.calldata bumpSel [a], callvalue := v, storage := σ }

/-- The gas bound of the two-block revert path: the loop checker's bound at two blocks. -/
abbrev G0 : Nat := AssembleLoop.gasBoundL Verify.LoopSource.Equiv.From.CtxGas.cx.base 2

/-- **R3, Counter is non-payable from every caller, value and storage.** For the checked
contract, every context `ctx.Ok` (caller below `2 ^ 160`, not the contract), every storage `σ`,
every argument `a < 2 ^ 256` and every call value `0 < v < 2 ^ 256`: SolidCore's runtime
dispatcher from `ctx.caller` at the statement's fuel rejects `bump(a)` (failure, no output, no
logs, storage `σ`), and EthLib runs the exact runtime bytes from `ctx.caller` to that same
observable at every gas from `G0` on. Gas is EthLib's message gas, a `Nat` with no upper bound. -/
def Statement : Prop :=
  ∀ c, contract? = .ok c → ∀ ctx : Context, ctx.Ok →
    ∀ (σ : List (Nat × Nat)) (a v : Nat), a < 2 ^ 256 → v < 2 ^ 256 → v ≠ 0 →
      Loop.runtimeRunFrom ctx.caller fuel c (bumpCallV σ a v) = some (Abi.rejected σ) ∧
        ∀ gas, G0 ≤ gas →
          runAt ctx gas (runtimeCode SolarTV.Export.Counter.bytecode) (bumpCallV σ a v) =
            some (Abi.rejected σ)

theorem counter_nonpayable : Statement := sorry

end Verify.AllValue.CounterValueChallenge
