import Contracts.UniswapV2.ERC20.SourceMirFromDefs

/-! The kernel's evaluation of the generic check of stage0 for transfer with the symbolic caller
(see SourceMirFrom.lean). -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec.UniswapV2.ERC20.SourceMir

kernel_rfl checkFrom_eq checkFrom? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

theorem checkFrom_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.checkSym SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fns = true := by
  have h := checkFrom_eq
  simp only [checkFrom?, checkFromOf, hc] at h
  exact h

end SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom
