import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#3 (obligation): loop invariant not satisfied on entry: exists uint256 j :: j < i && xs[j] == m. -/
theorem ob3 : SolarVerifyVc.ArrayMax.max.ob3.Valid := by
  vc_valid

end Contracts.ArrayMax.max
