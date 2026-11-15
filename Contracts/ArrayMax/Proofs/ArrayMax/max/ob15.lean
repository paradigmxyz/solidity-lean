import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#15 (obligation): postcondition not satisfied: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob15 : SolarVerifyVc.ArrayMax.max.ob15.Valid := by
  vc_valid

end Contracts.ArrayMax.max
