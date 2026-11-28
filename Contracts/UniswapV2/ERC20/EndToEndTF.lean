import Contracts.UniswapV2.ERC20.Lowering
import Verify.ShapeCtx
import uv2_erc20.ProofsATF.Stages
import uv2_erc20.Ctx

/-!
# UniswapV2ERC20's transferFrom: SolidCore's source to solar's exact runtime bytecode

The generic check accepts stage0 for `transferFrom` (`check_tf_ok`, `kernel_rfl`), and
`functional_tf` composes it with solar-tv's backend stages (on every call whose selector is none of
the ten functions other than approve, transfer and transferFrom) and the context checker's per-run
theorem on the exact bytecode: equivalence and termination of `transferFrom(from, to, value)` on
any argument words, no value, from the stage's caller, from any storage that writes
`DOMAIN_SEPARATOR`'s slot, under the context checker's named hypotheses on the message runner
(`StaticRunner`, `CalleesRun`). Its postcondition is the one given (`Post`), proved of the same
source runs: `True` here; the exported spec is ConnectTFSplit's.
-/

namespace SolidCore.Spec.UniswapV2.ERC20

open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Shapes

/-- `transferFrom(address,address,uint256)` as the stage's ABI sees it. -/
def fn_transferFrom : SolidCore.Refinement.Abi.Fn := ⟨599290589, List.replicate 3 (.uint 256)⟩

def fnsTF : List SolidCore.Refinement.Abi.Fn := [fn_transferFrom]

def checkTF? : Bool :=
  match SolidCore.Verify.VC.UniswapV2ERC20.contract? with
  | .ok c => Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fnsTF .all
  | .error _ => false

kernel_rfl checkTF_eq checkTF? true using SolidCore.Verify.VC.UniswapV2ERC20.selector_eq SolidCore.Verify.VC.mkIdx_eq SolidCore.Verify.VC.UniswapV2ERC20.digest_eq SolidCore.Spec.UniswapV2.ERC20.Keccak.keccakWord_eq

theorem check_tf_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fnsTF .all = true := by
  have h := checkTF_eq
  simp only [checkTF?, hc] at h
  exact h

theorem hscopeTF : ∀ call, genericValid0 fnsTF deployed call → SolarTV.Milestone.Uv2Erc20ATF.scope call := by
  rintro _ ⟨σ, -, f, hf, args, hlen, hargs, rfl⟩
  simp only [fnsTF, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  have h := (Generic.callFacts fn_transferFrom.sel (by decide) args hargs σ).selector
  simp only [SolarTV.Milestone.Uv2Erc20ATF.scope]
  rw [h]
  decide

/-- **transferFrom, from SolidCore's source to the exact bytecode**: equivalence and termination,
and any postcondition proved of the same source runs. -/
theorem functional_tf {Post : SolarTV.Call → SolarTV.Observable → Prop}
    (hP : ∀ gas, SolidCore.Refinement.Solar.AssembleCallSeg.StaticRunner gas)
    (hQ : ∀ gas call, genericValid0 fnsTF deployed call →
      SolidCore.Refinement.Solar.AssembleCallSeg.CalleesRun gas SolarTV.Export.UniswapV2ERC20.Ctx.code call)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c)
    (meets : Meets (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c (genericValid0 fnsTF deployed) Post) :
    Functional (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c SolarTV.Export.UniswapV2ERC20.Ctx.code
      (genericValid0 fnsTF deployed) (fun _ _ => True) Post := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  refine functional_ctx hdd (check_tf_ok hc) (base := SolarTV.Export.UniswapV2ERC20.Ctx.cx.base)
    (by decide) (genericValid0_inhabited fn_transferFrom [] deployed)
    (fun o => SolarTV.Milestone.Uv2Erc20ATF.uv2_erc20_atf_mir_to_evmir o) hscopeTF ?_ meets
  intro gas hg call hv
  obtain ⟨o, -, -, -, hok, hw⟩ := SolarTV.Export.UniswapV2ERC20.Ctx.bytecode [] _ hP hQ gas hg call hv
  exact ⟨o, hok, hw⟩

/-- Equivalence and termination of transferFrom, with no specification. -/
theorem compiled_tf
    (hP : ∀ gas, SolidCore.Refinement.Solar.AssembleCallSeg.StaticRunner gas)
    (hQ : ∀ gas call, genericValid0 fnsTF deployed call →
      SolidCore.Refinement.Solar.AssembleCallSeg.CalleesRun gas SolarTV.Export.UniswapV2ERC20.Ctx.code call) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Functional (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c SolarTV.Export.UniswapV2ERC20.Ctx.code
        (genericValid0 fnsTF deployed) (fun _ _ => True) (fun _ _ => True) := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  exact ⟨c, hc, functional_tf hP hQ hc fun _ _ _ _ => trivial⟩

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.compiled_tf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled_tf

end SolidCore.Spec.UniswapV2.ERC20
