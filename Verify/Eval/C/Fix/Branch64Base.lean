import Verify.Eval.C.Fix.Branch64Stmt
import Verify.Eval.Common.Measure

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace Verify.Eval.C.Fix.Branch64

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem base : stmt := by
  unfold stmt
  intro msg st ss x y hv
  have hfork : Fork.fusaka ≤ Fork.fusaka := by decide
  all_goals repeat symex_one [codeNat, codeSize] [hv] hfork

#proof_stats base
#kernel_recheck base

end Verify.Eval.C.Fix.Branch64
