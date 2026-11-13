import Examples.Token.VC.Transfer
import Examples.Token.VC.Mutant.SrcMut
import Examples.Token.VC.Mutant.SpecMut

/-!
# Mutants that break `transfer`'s binding

Two copies of `scripts/verify/Token.sol`, each changed in one line, exported by the same
solar-verify (`scripts/verify/mutant/MANIFEST`):
* `TokenSrcMut` changes the source: `transfer` credits `amount + 1`. solar-verify's encoding of the
  call's effect changes with it, so none of its obligations is the Lean obligation of
  `transfer`'s clauses, which `trStore_eval` ties to what SolidCore does with the real source.
* `TokenSpecMut` changes the spec: the recipient's clause claims `old + amount + 1`. Its obligation
  for that clause is not the one SolidCore's run supports.

In both, `checkScript` rejects, so no verdict on a mutant yields `transfer_triple`'s clauses.
-/

namespace SolidCore.Verify.VC.Token

open SolidCore.Verify.VC

theorem srcMut_rejects_to : checkScript Export.Mutant.TokenSrcMut.script [(trHyps, trGoalTo)] = false := by
  decide +kernel

theorem srcMut_rejects_from :
    checkScript Export.Mutant.TokenSrcMut.script [(trHyps, trGoalFrom)] = false := by
  decide +kernel

theorem srcMut_rejects_frame :
    checkScript Export.Mutant.TokenSrcMut.script [(trHyps, trGoalFrame)] = false := by
  decide +kernel

theorem specMut_rejects_to :
    checkScript Export.Mutant.TokenSpecMut.script [(trHyps, trGoalTo)] = false := by
  decide +kernel

/-- The unchanged clauses of the spec mutant still check: the rejection is the changed clause's. -/
theorem specMut_keeps_from_frame :
    checkScript Export.Mutant.TokenSpecMut.script [(trHyps, trGoalFrom), (trHyps, trGoalFrame)] = true := by
  decide +kernel

end SolidCore.Verify.VC.Token
