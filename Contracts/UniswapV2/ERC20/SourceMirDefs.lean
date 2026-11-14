import Contracts.UniswapV2.ERC20.Core
import Contracts.UniswapV2.ERC20.SpecTreeKeccak
import SolidCore.Refinement.Generic.Stage
import uv2_erc20.gen.UniswapV2ERC20.Stage0

/-! The definitions of E3 for UniswapV2ERC20.transfer (SourceMir.lean): the functions, the deployed
storage and the checks the kernel evaluates in SourceMirCheck and SourceMirDeploy, one module each
so that each Lean process stays within 6 GB. -/

namespace SolidCore.Spec.UniswapV2.ERC20.SourceMir

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- The steps along each path of the symbolic run of the module. -/
def mirFuel : Nat := 200

/-- `transfer(address,uint256)` as the stage's ABI sees it: its selector and two words. -/
def fn_transfer : Abi.Fn := ⟨2835717307, List.replicate 2 (.uint 256)⟩

/-- The functions of the stage. -/
def fns : List Abi.Fn := [fn_transfer]

/-- The storage the constructor leaves: `DOMAIN_SEPARATOR` (slot 3), the EIP-712 domain hash. -/
def deployed : List (Nat × Nat) := [(3, SolidCore.Spec.UniswapV2.ERC20.Keccak.kDomain)]

/-- Whether the generic check accepts `m` for `fns`, with the caller and Keccak-256 flags. -/
def checkOf (m : SolarTV.MIR.Lowered.Module) : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core m fns .all
  | .error _ => false

/-- Whether the generic check accepts stage0. -/
def check? : Bool := checkOf SolarTV.Export.UniswapV2ERC20.stage0

/-- Whether the contract deploys with `deployed` and no logs. -/
def deploy? : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Wide.deployedAt SolidCore.Verify.VC.UniswapV2ERC20.fuel c deployed
  | .error _ => false

end SolidCore.Spec.UniswapV2.ERC20.SourceMir
