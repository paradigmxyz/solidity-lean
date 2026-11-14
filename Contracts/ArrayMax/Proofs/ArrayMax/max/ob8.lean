import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#8 (obligation): loop invariant not preserved by the loop body: forall uint256 j :: j < i ==> xs[j] <= m. -/
theorem ob8 : SolarVerifyVc.ArrayMax.max.ob8.Valid := by
  vc_valid_prep <;> vc_bounded_leaf

end Contracts.ArrayMax.max
