import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#0 (obligation): loop invariant not satisfied on entry: 1 <= i. -/
theorem ob0 : SolarVerifyVc.ArrayMax.max.ob0.Valid := by
  vc_valid

end Contracts.ArrayMax.max
