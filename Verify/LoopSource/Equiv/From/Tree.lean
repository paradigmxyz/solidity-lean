import Verify.LoopSource.Equiv.From.Bump
import Contracts.VerifyCounter.SourceBump
import Verify.LoopSource.Equiv.Counter.Summary

/-!
# The symbolic-caller summary has the default summary's tree

`bumpBr` here differs from `Contracts.VerifyCounter.Source.bumpBr` only in its leaves' `caller`
field, which a tree does not record, so both make the same tree (`tree_eq`, by the kernel).
-/

namespace Verify.LoopSource.Equiv.From
open SolidCore.Refinement.Generic

theorem tree_eq :
    brTree CounterSummary.fn (argFacts [256] 0) bumpBr =
      brTree CounterSummary.fn (argFacts [256] 0) Contracts.VerifyCounter.Source.bumpBr := by
  decide +kernel

end Verify.LoopSource.Equiv.From
