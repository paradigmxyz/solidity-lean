import Contracts.UniswapV2.ERC20.SourceMirDefs
import uv2_erc20.gen.UniswapV2ERC20Mut.PinnedCaller

/-! The fixed-caller check accepts `PinnedCaller` (stage0 with `CALLER` replaced by `0x2000`): a stage
for one caller does not tell such code apart; `SourceMirFromNeg.refuses_PinnedCaller` shows the check
for every caller does. -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirPinned

open SolidCore.Spec.UniswapV2.ERC20.SourceMir

/-- The fixed-caller check of `PinnedCaller`. -/
def pinnedFixed? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.PinnedCaller.stage0

kernel_rfl pinned_fixed_accepts pinnedFixed? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

end SolidCore.Spec.UniswapV2.ERC20.SourceMirPinned
