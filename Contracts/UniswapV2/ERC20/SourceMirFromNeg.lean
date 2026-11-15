import Contracts.UniswapV2.ERC20.SourceMirFromDefs
import uv2_erc20.gen.UniswapV2ERC20Mut.NoDebit
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongSlot
import uv2_erc20.gen.UniswapV2ERC20Mut.NoOverflowCheck
import uv2_erc20.gen.UniswapV2ERC20Mut.NoUnderflowCheck
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongTopic
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongReturn
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongRevertData
import uv2_erc20.gen.UniswapV2ERC20Mut.SwappedLogArgs
import uv2_erc20.gen.UniswapV2ERC20Mut.PinnedCaller

/-!
# Negative controls of E3 for transfer from every caller

The kernel evaluates `Generic.checkSym` (the check with the symbolic caller) of each stage0 mutant of
scripts/verify/uniswap_v2_erc20_mutants.py, against the same checked source, to `false`.

`PinnedCaller` replaces transfer's `CALLER` with the constant `0x2000` (`callerAddress`): code that is
right only when the caller is `callerAddress`. The fixed-caller check (`SourceMir.checkOf`, which
erases `msg.sender` to that same constant) **accepts** it (`pinned_fixed_accepts`), and the check for
every caller refuses it (`refuses_PinnedCaller`): the generalisation is not vacuous.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirFromNeg

open SolidCore.Spec.UniswapV2.ERC20.SourceMirFrom

/-- The check for every caller refuses the mutant `NoDebit`. -/
def NoDebit? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.NoDebit.stage0

kernel_rfl refuses_NoDebit NoDebit? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `WrongSlot`. -/
def WrongSlot? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.WrongSlot.stage0

kernel_rfl refuses_WrongSlot WrongSlot? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `NoOverflowCheck`. -/
def NoOverflowCheck? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.NoOverflowCheck.stage0

kernel_rfl refuses_NoOverflowCheck NoOverflowCheck? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `NoUnderflowCheck`. -/
def NoUnderflowCheck? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.NoUnderflowCheck.stage0

kernel_rfl refuses_NoUnderflowCheck NoUnderflowCheck? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `WrongTopic`. -/
def WrongTopic? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.WrongTopic.stage0

kernel_rfl refuses_WrongTopic WrongTopic? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `WrongReturn`. -/
def WrongReturn? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.WrongReturn.stage0

kernel_rfl refuses_WrongReturn WrongReturn? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `WrongRevertData`. -/
def WrongRevertData? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.WrongRevertData.stage0

kernel_rfl refuses_WrongRevertData WrongRevertData? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `SwappedLogArgs`. -/
def SwappedLogArgs? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.SwappedLogArgs.stage0

kernel_rfl refuses_SwappedLogArgs SwappedLogArgs? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check for every caller refuses the mutant `PinnedCaller`. -/
def PinnedCaller? : Bool := checkFromOf SolarTV.Export.UniswapV2ERC20Mut.PinnedCaller.stage0

kernel_rfl refuses_PinnedCaller PinnedCaller? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

end SolidCore.Spec.UniswapV2.ERC20.SourceMirFromNeg
