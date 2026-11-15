import Contracts.UniswapV2.ERC20.SourceMirDefs
import SolidCore.Refinement.Generic.StageFrom

/-! The definitions of E3 for UniswapV2ERC20.transfer from every caller (SourceMirFrom.lean): the
check with the symbolic caller, which SourceMirFromCheck evaluates in the kernel. -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec.UniswapV2.ERC20.SourceMir

/-- Whether the generic check with the symbolic caller accepts `m` for transfer. -/
def checkFromOf (m : SolarTV.MIR.Lowered.Module) : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.checkSym SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core m fns
  | .error _ => false

/-- Whether it accepts stage0. -/
def checkFrom? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20.stage0

end SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom
