import Contracts.VerifyCounter.Bump

/-!
# VerifyCounter's bump: the declared valid calls of the published statement

Reviewed input of `Certified/verify_counter/shape.json`, not proof: the valid calls are
`bump(n)` (`Bump.IsBump`, the selector) with `n < 2 ^ 32`, the range where the proved gas bound
`Bump.gasBound` (linear in `n`) stays below `2 ^ 64`.
-/

namespace Contracts.VerifyCounter.ShapeSpec

open SolarTV.Milestone.VerifyCounter.Bump

/-- The declared valid calls: `bump(n)` with `n < 2 ^ 32`. -/
def ValidB (call : SolarTV.Call) : Prop :=
  IsBump call ∧ (SolarTV.Machine.calldataWord call 4).toNat < 2 ^ 32

end Contracts.VerifyCounter.ShapeSpec
