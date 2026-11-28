import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.clamp

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of ArrayMax.clamp, as the frozen v1 export states them
(`Vc/ArrayMax/clamp.lean`). -/

namespace Contracts.ArrayMax.clamp

/-- ArrayMax.clamp#1 (obligation): postcondition not satisfied: r <= n. -/
theorem ob1 : SolarVerifyVc.ArrayMax.clamp.ob1.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.ArrayMax.clamp
