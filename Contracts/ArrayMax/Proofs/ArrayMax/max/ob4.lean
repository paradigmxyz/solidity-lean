import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#4 (obligation): loop invariant not satisfied on entry: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob4 : SolarVerifyVc.ArrayMax.max.ob4.Valid := by
  vc_valid

end Contracts.ArrayMax.max
