import Contracts.ArrayMax.Bounded
import Contracts.Vault.Vc.Vault.deposit

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of Vault.deposit, as the frozen v1 export states them
(`Vc/Vault/deposit.lean`). -/

namespace Contracts.Vault.deposit

/-- Vault.deposit#0 (side): side. -/
theorem ob0 : SolarVerifyVc.Vault.deposit.ob0.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#2 (obligation): postcondition not satisfied: shares[msg.sender] == old(shares[msg.sender]) + amount. -/
theorem ob2 : SolarVerifyVc.Vault.deposit.ob2.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#3 (obligation): postcondition not satisfied: !locked. -/
theorem ob3 : SolarVerifyVc.Vault.deposit.ob3.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#4 (obligation): contract invariant not preserved: totalShares == sumShares. -/
theorem ob4 : SolarVerifyVc.Vault.deposit.ob4.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#5 (obligation): contract invariant not preserved: totalShares <= totalAssets. -/
theorem ob5 : SolarVerifyVc.Vault.deposit.ob5.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#6 (side): side. -/
theorem ob6 : SolarVerifyVc.Vault.deposit.ob6.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.deposit#7 (obligation): entry point does not revert while reentrancy guard 'locked' is held. -/
theorem ob7 : SolarVerifyVc.Vault.deposit.ob7.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.Vault.deposit
