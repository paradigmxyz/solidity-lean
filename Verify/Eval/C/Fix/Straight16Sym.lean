import Verify.Eval.C.Fix.Straight16Stmt
import Verify.Eval.C.Stepper
import Verify.Eval.Common.Measure

namespace Verify.Eval.C.Fix.Straight16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sym : stmt := by
  unfold stmt
  evm_sym [codeNat, codeSize]

#proof_stats sym
#kernel_recheck sym

end Verify.Eval.C.Fix.Straight16
