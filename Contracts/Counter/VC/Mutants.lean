import Contracts.Counter.VC.Inc
import Contracts.Counter.VC.Mutant.SrcMut
import Contracts.Counter.VC.Mutant.SpecMut

/-!
# Mutants that break `Counter.inc`'s binding

Two copies of `scripts/verify/CounterMilestone.sol`, each changed in one line and exported by the same
solar-verify (`scripts/verify/mutant/MANIFEST`):
* `CounterSrcMut` changes the source to `x += d + 1`. solar-verify's encoding of the new `x` changes with
  it, so none of its obligations is `incHyps ⟹ incGoal`, whose effect term `incEff` is the one
  `inc_binding` ties to what SolidCore runs on the real source.
* `CounterSpecMut` changes the spec to `x == old(x) + d + 1`. Its obligation's goal is not `incGoal`.

`checkScript` rejects both, so neither script is bound to SolidCore's `Counter`.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify.VC

theorem srcMut_rejected : checkScript Export.Mutant.CounterSrcMut.script [(incHyps, incGoal)] = false := by
  decide +kernel

theorem specMut_rejected : checkScript Export.Mutant.CounterSpecMut.script [(incHyps, incGoal)] = false := by
  decide +kernel

end SolidCore.Verify.VC.Counter
