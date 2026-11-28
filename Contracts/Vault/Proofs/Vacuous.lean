import Contracts.ArrayMax.Bounded
import Contracts.Vault.Vc.Vault.deposit
import Contracts.Vault.Vc.Vault.withdraw

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! Vault's vacuous obligations. Each theorem proves that the obligation's assertions and guard
alone are unsatisfiable: the obligation with its goal replaced by `false` is valid. These
obligations therefore hold whatever their goal says, and their proofs (Proofs/Vault/) are no
evidence about the goal. They are the paths that start with the reentrancy guard `locked` held,
which the contract invariant and the entry point's own check exclude. -/

namespace Contracts.Vault.Vacuous

open SolarVerify.Vc SolarVerify.Smt

/-- The obligation with goal `false`: valid exactly when its hypotheses refute. -/
def refute (o : Obligation) : Obligation := { o with goal := .bool false }

/-- Vault.deposit#6 (side): its hypotheses refute. -/
theorem deposit_ob6 : (refute SolarVerifyVc.Vault.deposit.ob6).Valid := by
  unfold refute; first | vc_bounded_valid | vc_valid

/-- Vault.deposit#7: its hypotheses refute (its goal is already `false`). -/
theorem deposit_ob7 : (refute SolarVerifyVc.Vault.deposit.ob7).Valid := by
  unfold refute; first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#6: its hypotheses refute. -/
theorem withdraw_ob6 : (refute SolarVerifyVc.Vault.withdraw.ob6).Valid := by
  unfold refute; first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#7 (side): its hypotheses refute. -/
theorem withdraw_ob7 : (refute SolarVerifyVc.Vault.withdraw.ob7).Valid := by
  unfold refute; first | vc_bounded_valid | vc_valid

/-- Vault.withdraw#8: its hypotheses refute (its goal is already `false`). -/
theorem withdraw_ob8 : (refute SolarVerifyVc.Vault.withdraw.ob8).Valid := by
  unfold refute; first | vc_bounded_valid | vc_valid

end Contracts.Vault.Vacuous
