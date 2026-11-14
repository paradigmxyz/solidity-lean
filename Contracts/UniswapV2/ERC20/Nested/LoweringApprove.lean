import Contracts.UniswapV2.ERC20.Nested.Trees
import SolidCore.Refinement.Generic.Stage
import SolidCore.Refinement.Generic.Total
import uv2_erc20.gen.UniswapV2ERC20.Stage0

/-!
# UniswapV2ERC20.approve: SolidCore's source to solar's first lowered MIR (edge E3)

`check_approve_ok`: the generic source check (`Generic.check`, every environment flag) accepts
`SolarTV.Export.UniswapV2ERC20.stage0`, solar's first lowered MIR of the same pinned source
(scripts/verify/uniswap_v2_erc20_stages.sh, `-Ogas --evm-version osaka`), for `approve` alone, against
SolidCore's checked contract, evaluated by the kernel from the source text up (`kernel_rfl`).
`approve_source_to_mir` is the stage it gives: under every oracle whose caller and two-word Keccak-256
are SolidCore's (`Generic.SourceEnvOk`), every SolidCore result on a valid call of approve (any argument
words, no value, any storage covering the deployed one) is stage0's; `approve_defined`: SolidCore has a
result on each (termination within the fuel, by the checker, not by a fuel premise).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Nested

open SolidCore.Refinement SolidCore.Refinement.Generic

/-- The steps along each path of the symbolic run of stage0. -/
def mirFuel : Nat := 200

def checkapprove? : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 [fn_approve] .all
  | .error _ => false

kernel_rfl checkapprove_eq checkapprove? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

theorem check_approve_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 [fn_approve] .all = true := by
  have h := checkapprove_eq
  simp only [checkapprove?, hc] at h
  exact h

/-- **E3 for approve**: SolidCore's checked source to solar's stage0, on approve's valid calls. -/
theorem approve_source_to_mir (o : SolarTV.Machine.Oracle) (ho : Generic.SourceEnvOk o)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0
      (fun call => ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_approve] σ call) := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  exact stageAtWith o hdd ho.ask (check_approve_ok hc)

/-- SolidCore has a result on every valid call of approve. -/
theorem approve_defined {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Defined (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c
      (fun call => ∃ σ, Covers deployed σ ∧ SolidCore.Refinement.Abi.fullScope [fn_approve] σ call) := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  exact definedAt hdd (check_approve_ok hc)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Nested.approve_source_to_mir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms approve_source_to_mir

end SolidCore.Spec.UniswapV2.ERC20.Nested
