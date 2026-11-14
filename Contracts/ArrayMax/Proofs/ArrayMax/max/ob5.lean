import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#5 (obligation): loop invariant not satisfied on entry: xs.length > 0. -/
theorem ob5 : SolarVerifyVc.ArrayMax.max.ob5.Valid := by
  vc_valid

end Contracts.ArrayMax.max
