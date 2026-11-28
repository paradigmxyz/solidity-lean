import Contracts.UniswapV2.ERC20.Nested.LoweringTransferFrom
import uv2_erc20.gen.UniswapV2ERC20.Stage0Mut1
import uv2_erc20.gen.UniswapV2ERC20.Stage0Mut2
import uv2_erc20.gen.UniswapV2ERC20.Stage0Mut3

/-!
# Negative controls of E3 for approve and transferFrom, by execution

The generic source check that accepts solar's stage0 (`check_approve_ok`, `check_transferFrom_ok`)
refuses, by the kernel's evaluation, three mutants of that same stage0
(scripts/verify/uniswap_v2_stage0_mutants.py): `_approve` with its SSTORE of
`allowance[owner][spender]` dropped (`rejects_approve_no_write`), `_approve` hashing the owner into
mapping slot 3 instead of allowance's slot 2 (`rejects_approve_wrong_slot`), and `transferFrom` with
the SSTORE of the spent allowance dropped (`rejects_transferFrom_no_spend`). Each is a mismatch of the
symbolic run against the source's tree, `false`, never a timeout.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolidCore.Refinement SolidCore.Refinement.Generic

def checkMut? (m : SolarTV.MIR.Lowered.Module) (fn : SolidCore.Refinement.Abi.Fn) : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core m [fn] .all
  | .error _ => true

def checkMut1? : Bool := checkMut? SolarTV.Export.UniswapV2ERC20Mut1.stage0 fn_approve
def checkMut2? : Bool := checkMut? SolarTV.Export.UniswapV2ERC20Mut2.stage0 fn_approve
def checkMut3? : Bool := checkMut? SolarTV.Export.UniswapV2ERC20Mut3.stage0 fn_transferFrom

kernel_rfl rejects_approve_no_write checkMut1? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq
kernel_rfl rejects_approve_wrong_slot checkMut2? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq
kernel_rfl rejects_transferFrom_no_spend checkMut3? false using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

end SolidCore.Spec.UniswapV2.ERC20.Nested
