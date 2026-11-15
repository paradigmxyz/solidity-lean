import Contracts.UniswapV2.ERC20.Connect
import SolidCore.Refinement.Generic.Stage
import uv2_erc20.gen.UniswapV2ERC20.Stage0

/-!
# UniswapV2ERC20: the generic source stage to solar's first lowered MIR, for approve and transfer

`check_eq`: the generic check (`Generic.check` with the caller and the hash of two words) accepts
`SolarTV.Export.UniswapV2ERC20.stage0`, solar's first lowered MIR of the same file, for `approve`
and `transfer` against SolidCore's checked contract, evaluated by the kernel from the source text
up (`kernel_rfl`, with the selector, event-topic and Keccak-256 tables each entry of which the
kernel checks once).
-/

namespace SolidCore.Spec.UniswapV2.ERC20

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- The steps along each path of the symbolic run of the module. -/
def mirFuel : Nat := 200

/-- The functions of the statement. -/
def fns : List SolidCore.Refinement.Abi.Fn := [fn_approve, fn_transfer]

/-- Whether the generic check accepts stage0 for `fns`. -/
def check? : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fns .all
  | .error _ => false

kernel_rfl check_eq check? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

theorem check_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fns .all = true := by
  have h := check_eq
  simp only [check?, hc] at h
  exact h

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.check_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms check_ok

end SolidCore.Spec.UniswapV2.ERC20
