import Verify.LoopSource.Equiv.EraseLoopCounter
import Contracts.VerifyCounter.SourceBump

/-!
# The restated `bump` is the type checker's

`EraseLoopCounter` restates `bump`'s body and `Counter`'s storage fields so that its test imports no
hand-written loop proof. This module checks, by `rfl`, that they are the values
`Contracts.VerifyCounter.Source` ties to the checked contract (its `shape_eq` and `kernel_rfl`
checks say the checked `Counter`'s fields are `vcFields` and its `bump(uint256)` has the body
`bumpBody`). It only compares definitions; nothing in `EraseLoopCounter` depends on it.
-/

namespace Verify.LoopSource.Equiv.EraseLoopCounter

theorem bumpBody_eq : bumpBody = Contracts.VerifyCounter.Source.bumpBody := rfl

theorem fields_eq : fields = Contracts.VerifyCounter.Source.vcFields := rfl

end Verify.LoopSource.Equiv.EraseLoopCounter
