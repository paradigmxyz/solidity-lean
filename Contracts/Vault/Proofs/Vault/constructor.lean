import Contracts.ArrayMax.Bounded
import Contracts.Vault.Vc.Vault.constructor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Kernel proofs of the required obligations of Vault.constructor, as the frozen v1 export states them
(`Vc/Vault/constructor.lean`). -/

namespace Contracts.Vault.constructor

/-- Vault.constructor#1 (obligation): contract invariant not established by constructor: totalShares == sumShares. -/
theorem ob1 : SolarVerifyVc.Vault.constructor.ob1.Valid := by
  first | vc_bounded_valid | vc_valid

/-- Vault.constructor#2 (obligation): contract invariant not established by constructor: totalShares <= totalAssets. -/
theorem ob2 : SolarVerifyVc.Vault.constructor.ob2.Valid := by
  first | vc_bounded_valid | vc_valid

end Contracts.Vault.constructor
