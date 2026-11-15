import Contracts.UniswapV2.ERC20.SourceMirDefs

/-! The kernel's evaluation of UniswapV2ERC20's deployment: the constructor leaves exactly
`deployed` and no logs (see SourceMir.lean). -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec.UniswapV2.ERC20.SourceMir

kernel_rfl deploy_eq deploy? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq


end SolidCore.Spec.UniswapV2.ERC20.SourceMirDeploy
