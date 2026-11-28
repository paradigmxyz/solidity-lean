import Contracts.UniswapV2.ERC20.Nested.Trees
import SolidCore.Refinement.Generic.Stage
import SolidCore.Refinement.Generic.Total
import uv2_erc20.gen.UniswapV2ERC20.Stage0
import Contracts.UniswapV2.ERC20.Nested.LoweringApprove

/-!
# UniswapV2ERC20.transferFrom: SolidCore's source to solar's first lowered MIR (edge E3)

`check_transferFrom_ok`: the generic source check (`Generic.check`, every environment flag) accepts
`SolarTV.Export.UniswapV2ERC20.stage0`, solar's first lowered MIR of the same pinned source
(scripts/verify/uniswap_v2_erc20_stages.sh, `-Ogas --evm-version osaka`), for `transferFrom` alone, against
SolidCore's checked contract, evaluated by the kernel from the source text up (`kernel_rfl`).
`transferFrom_source_to_mir` is the stage it gives: under every oracle whose caller and two-word Keccak-256
are SolidCore's (`Generic.SourceEnvOk`), every SolidCore result on a valid call of transferFrom (any argument
words, no value, any storage covering the deployed one) is stage0's; `transferFrom_defined`: SolidCore has a
result on each (termination within the fuel, by the checker, not by a fuel premise).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolidCore.Refinement SolidCore.Refinement.Generic

def checktransferFrom? : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 [fn_transferFrom] .all
  | .error _ => false

kernel_rfl checktransferFrom_eq checktransferFrom? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

theorem check_transferFrom_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 [fn_transferFrom] .all = true := by
  have h := checktransferFrom_eq
  simp only [checktransferFrom?, hc] at h
  exact h

/-- **E3 for transferFrom**: SolidCore's checked source to solar's stage0, on transferFrom's valid calls. -/
theorem transferFrom_source_to_mir (o : SolarTV.Machine.Oracle) (ho : Generic.SourceEnvOk o)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0
      (fun call => ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_transferFrom] σ call) := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  exact stageAtWith o hdd ho.ask (check_transferFrom_ok hc)

/-- SolidCore has a result on every valid call of transferFrom. -/
theorem transferFrom_defined {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Defined (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c
      (fun call => ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_transferFrom] σ call) := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  exact definedAt hdd (check_transferFrom_ok hc)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Nested.transferFrom_source_to_mir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transferFrom_source_to_mir

end SolidCore.Spec.UniswapV2.ERC20.Nested
