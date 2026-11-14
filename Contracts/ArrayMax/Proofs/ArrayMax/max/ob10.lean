import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#10 (obligation): loop invariant not preserved by the loop body: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob10 : SolarVerifyVc.ArrayMax.max.ob10.Valid := by
  vc_valid_prep <;> vc_bounded

end Contracts.ArrayMax.max
