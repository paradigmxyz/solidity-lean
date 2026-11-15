import Verify.Eval.C.Fix.Straight32Stmt
import Verify.Eval.Common.Measure

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex

namespace Verify.Eval.C.Fix.Straight32

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem base : stmt := by
  unfold stmt
  intro msg st ss x y
  repeat evm_step [codeNat, codeSize]
  refine revert_empty (by decide) ?_ ?_ <;> evm_code [codeNat, codeSize]

#proof_stats base
#kernel_recheck base

end Verify.Eval.C.Fix.Straight32
