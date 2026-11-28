import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMaxEntry.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of ArrayMaxEntry.max, as the frozen v1 export states them
(`Vc/ArrayMaxEntry/max.lean`). -/

namespace Contracts.ArrayMaxEntry.max

/-- ArrayMaxEntry.max#0 (obligation): precondition of 'max' not satisfied: xs.length > 0. -/
theorem ob0 : SolarVerifyVc.ArrayMaxEntry.max.ob0.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMaxEntry.max#2 (obligation): postcondition not satisfied: forall uint256 j :: j < xs.length ==> xs[j] <= result. -/
theorem ob2 : SolarVerifyVc.ArrayMaxEntry.max.ob2.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMaxEntry.max#3 (obligation): postcondition not satisfied: exists uint256 j :: j < xs.length && xs[j] == result. -/
theorem ob3 : SolarVerifyVc.ArrayMaxEntry.max.ob3.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.ArrayMaxEntry.max
