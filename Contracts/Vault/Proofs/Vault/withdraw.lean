import Contracts.ArrayMax.Bounded
import Contracts.Vault.Vc.Vault.withdraw

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of Vault.withdraw, as the frozen v1 export states them
(`Vc/Vault/withdraw.lean`). -/

namespace Contracts.Vault.withdraw

/-- Vault.withdraw#0 (obligation): assertion failed: totalShares == sumShares && totalShares <= totalAssets. -/
theorem ob0 : SolarVerifyVc.Vault.withdraw.ob0.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#1 (side): side. -/
theorem ob1 : SolarVerifyVc.Vault.withdraw.ob1.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#3 (obligation): postcondition not satisfied: !locked. -/
theorem ob3 : SolarVerifyVc.Vault.withdraw.ob3.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#4 (obligation): contract invariant not preserved: totalShares == sumShares. -/
theorem ob4 : SolarVerifyVc.Vault.withdraw.ob4.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#5 (obligation): contract invariant not preserved: totalShares <= totalAssets. -/
theorem ob5 : SolarVerifyVc.Vault.withdraw.ob5.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#6 (obligation): assertion failed: totalShares == sumShares && totalShares <= totalAssets. -/
theorem ob6 : SolarVerifyVc.Vault.withdraw.ob6.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#7 (side): side. -/
theorem ob7 : SolarVerifyVc.Vault.withdraw.ob7.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#8 (obligation): entry point does not revert while reentrancy guard 'locked' is held. -/
theorem ob8 : SolarVerifyVc.Vault.withdraw.ob8.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.Vault.withdraw
