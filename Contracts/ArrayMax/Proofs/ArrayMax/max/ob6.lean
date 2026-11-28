import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#6 (obligation): loop invariant not preserved by the loop body: 1 <= i. -/
theorem ob6 : SolarVerifyVc.ArrayMax.max.ob6.Valid := by
  vc_valid

end Contracts.ArrayMax.max
