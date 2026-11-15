import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#11 (obligation): loop invariant not preserved by the loop body: xs.length > 0. -/
theorem ob11 : SolarVerifyVc.ArrayMax.max.ob11.Valid := by
  vc_valid

end Contracts.ArrayMax.max
