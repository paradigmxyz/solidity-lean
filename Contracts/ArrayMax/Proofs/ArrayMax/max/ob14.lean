import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#14 (obligation): postcondition not satisfied: forall uint256 j :: j < xs.length ==> xs[j] <= m. -/
theorem ob14 : SolarVerifyVc.ArrayMax.max.ob14.Valid := by
  vc_bounded_valid

end Contracts.ArrayMax.max
