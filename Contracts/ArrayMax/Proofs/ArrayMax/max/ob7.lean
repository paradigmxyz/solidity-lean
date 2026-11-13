import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#7 (obligation): loop invariant not preserved by the loop body: i <= xs.length. -/
theorem ob7 : SolarVerifyVc.ArrayMax.max.ob7.Valid := by
  vc_valid

end Contracts.ArrayMax.max
