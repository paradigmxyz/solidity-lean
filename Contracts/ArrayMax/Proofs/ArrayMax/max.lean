import Contracts.ArrayMax.Bounded
import Contracts.ArrayMax.Vc.ArrayMax.max

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of ArrayMax.max, as the frozen v1 export states them
(`Vc/ArrayMax/max.lean`). -/

namespace Contracts.ArrayMax.max

/-- ArrayMax.max#0 (obligation): loop invariant not satisfied on entry: 1 <= i. -/
theorem ob0 : SolarVerifyVc.ArrayMax.max.ob0.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#1 (obligation): loop invariant not satisfied on entry: i <= xs.length. -/
theorem ob1 : SolarVerifyVc.ArrayMax.max.ob1.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#2 (obligation): loop invariant not satisfied on entry: forall uint256 j :: j < i ==> xs[j] <= m. -/
theorem ob2 : SolarVerifyVc.ArrayMax.max.ob2.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#3 (obligation): loop invariant not satisfied on entry: exists uint256 j :: j < i && xs[j] == m. -/
theorem ob3 : SolarVerifyVc.ArrayMax.max.ob3.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#4 (obligation): loop invariant not satisfied on entry: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob4 : SolarVerifyVc.ArrayMax.max.ob4.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#5 (obligation): loop invariant not satisfied on entry: xs.length > 0. -/
theorem ob5 : SolarVerifyVc.ArrayMax.max.ob5.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#6 (obligation): loop invariant not preserved by the loop body: 1 <= i. -/
theorem ob6 : SolarVerifyVc.ArrayMax.max.ob6.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#7 (obligation): loop invariant not preserved by the loop body: i <= xs.length. -/
theorem ob7 : SolarVerifyVc.ArrayMax.max.ob7.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#8 (obligation): loop invariant not preserved by the loop body: forall uint256 j :: j < i ==> xs[j] <= m. -/
theorem ob8 : SolarVerifyVc.ArrayMax.max.ob8.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#9 (obligation): loop invariant not preserved by the loop body: exists uint256 j :: j < i && xs[j] == m. -/
theorem ob9 : SolarVerifyVc.ArrayMax.max.ob9.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#10 (obligation): loop invariant not preserved by the loop body: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob10 : SolarVerifyVc.ArrayMax.max.ob10.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#11 (obligation): loop invariant not preserved by the loop body: xs.length > 0. -/
theorem ob11 : SolarVerifyVc.ArrayMax.max.ob11.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#12 (obligation): loop does not terminate: decreases clause not decreased: (xs.length) - i. -/
theorem ob12 : SolarVerifyVc.ArrayMax.max.ob12.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#14 (obligation): postcondition not satisfied: forall uint256 j :: j < xs.length ==> xs[j] <= m. -/
theorem ob14 : SolarVerifyVc.ArrayMax.max.ob14.Valid := by
  first | vc_bounded_valid | vc_valid

/-- ArrayMax.max#15 (obligation): postcondition not satisfied: exists uint256 j :: j < xs.length && xs[j] == m. -/
theorem ob15 : SolarVerifyVc.ArrayMax.max.ob15.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.ArrayMax.max
