import Contracts.UniswapV2.ERC20.SourceMirDefs

/-! The kernel's evaluation of the generic check of stage0 for transfer (see SourceMir.lean). -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMir

open SolidCore.Refinement SolidCore.Refinement.Generic

kernel_rfl check_eq check? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq


theorem check_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fns .all = true := by
  have h := check_eq
  simp only [check?, checkOf, hc] at h
  exact h

end SolidCore.Spec.UniswapV2.ERC20.SourceMir
