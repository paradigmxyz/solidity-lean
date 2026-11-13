import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#12 (obligation): loop does not terminate: decreases clause not decreased: (xs.length) - i. -/
theorem ob12 : SolarVerifyVc.ArrayMax.max.ob12.Valid := by
  vc_valid

end Contracts.ArrayMax.max
