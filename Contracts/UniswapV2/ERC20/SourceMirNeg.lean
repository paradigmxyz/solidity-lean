import Contracts.UniswapV2.ERC20.SourceMirDefs
import uv2_erc20.gen.UniswapV2ERC20Mut.NoDebit
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongSlot
import uv2_erc20.gen.UniswapV2ERC20Mut.NoOverflowCheck
import uv2_erc20.gen.UniswapV2ERC20Mut.NoUnderflowCheck
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongTopic
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongReturn
import uv2_erc20.gen.UniswapV2ERC20Mut.WrongRevertData
import uv2_erc20.gen.UniswapV2ERC20Mut.SwappedLogArgs

/-!
# Negative controls of E3 for transfer: mutated MIR refused by the kernel's evaluation

Each mutant is solar's exported stage0 with one instruction of `transfer`, `_transfer` or SafeMath's
`sub` edited (scripts/verify/uniswap_v2_erc20_mutants.py, which fails if an edit does not apply),
and the kernel evaluates the same generic check of it, against the same checked source, to `false`:
the check that accepts stage0 (`SourceMir.check_eq`) does not accept a debit dropped, a wrong
mapping slot, either overflow test reversed, a wrong event topic, swapped topic arguments, a wrong
return value or wrong revert data.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMirNeg

open SolidCore.Spec.UniswapV2.ERC20.SourceMir

/-- The check refuses the mutant `NoDebit`. -/
def NoDebit? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.NoDebit.stage0

kernel_rfl refuses_NoDebit NoDebit? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `WrongSlot`. -/
def WrongSlot? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.WrongSlot.stage0

kernel_rfl refuses_WrongSlot WrongSlot? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `NoOverflowCheck`. -/
def NoOverflowCheck? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.NoOverflowCheck.stage0

kernel_rfl refuses_NoOverflowCheck NoOverflowCheck? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `NoUnderflowCheck`. -/
def NoUnderflowCheck? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.NoUnderflowCheck.stage0

kernel_rfl refuses_NoUnderflowCheck NoUnderflowCheck? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `WrongTopic`. -/
def WrongTopic? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.WrongTopic.stage0

kernel_rfl refuses_WrongTopic WrongTopic? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `WrongReturn`. -/
def WrongReturn? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.WrongReturn.stage0

kernel_rfl refuses_WrongReturn WrongReturn? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `WrongRevertData`. -/
def WrongRevertData? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.WrongRevertData.stage0

kernel_rfl refuses_WrongRevertData WrongRevertData? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

/-- The check refuses the mutant `SwappedLogArgs`. -/
def SwappedLogArgs? : Bool := checkOf SolarTV.Export.UniswapV2ERC20Mut.SwappedLogArgs.stage0

kernel_rfl refuses_SwappedLogArgs SwappedLogArgs? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

end SolidCore.Spec.UniswapV2.ERC20.SourceMirNeg

