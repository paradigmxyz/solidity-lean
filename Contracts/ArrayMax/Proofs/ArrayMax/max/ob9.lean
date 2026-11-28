import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#9 (obligation): loop invariant not preserved by the loop body: exists uint256 j :: j < i && xs[j] == m. -/
theorem ob9 : SolarVerifyVc.ArrayMax.max.ob9.Valid := by
  vc_bounded_valid

end Contracts.ArrayMax.max
