import Contracts.UniswapV2.ERC20.EndToEnd
import Contracts.UniswapV2.ERC20.EndToEndTFSpec

/-!
# UniswapV2ERC20's approve, transfer and transferFrom: one theorem on the exact runtime bytecode

`published`: `Shapes.Functional` (equivalence at every gas below `2 ^ 256`, termination and the
exported specs) of SolidCore's checked `UniswapV2ERC20` and the exact runtime bytecode solar emitted
for it (2187 bytes, `SolarTV.Export.UniswapV2ERC20.Ctx.code`), on the valid calls of all three
functions: any argument words below `2 ^ 256`, no value, the stage's caller, any storage that
writes the slot the constructor wrote. It composes, by `Shapes.functional_ctx` alone, the generic
source stage for the three functions (`check_ok` and `check_tf_ok`, joined by `List.all_append`),
solar-tv's backend stages whose scope covers the three selectors (`Uv2Erc20ATF`), the context
checker's per-run theorem and solar-verify's exported specs of the three functions.

Named hypotheses, all in the statement: `NestedSlotsSeparated [1, 4] [2]` (keccak256 injective with large
images on the mapping slots; specification only), `AssembleCallSeg.StaticRunner` at every gas and
`AssembleCallSeg.CalleesRun` on the valid calls (equivalence only).

Not covered: resources (no gas bound, so not `Shapes.Certified`), `permit`, the getters, the
constructor (only through the storage it leaves), callers other than the stage's.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.EndToEndAll

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec.UniswapV2.ERC20

/-- The functions of the statement. -/
def fns3 : List SolidCore.Refinement.Abi.Fn := [fn_approve, fn_transfer, fn_transferFrom]

/-- The specification: the exported specs of approve, transfer and transferFrom. -/
def Post (call : SolarTV.Call) (obs : SolarTV.Observable) : Prop :=
  EndToEnd.Post call obs ∧ EndToEndTF.Post call obs

theorem check3_ok {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    Generic.check SolidCore.Verify.VC.UniswapV2ERC20.fuel mirFuel c.core
      SolarTV.Export.UniswapV2ERC20.stage0 fns3 .all = true := by
  have h1 := check_ok hc
  have h2 := check_tf_ok hc
  unfold Generic.check at h1 h2 ⊢
  rw [show fns3 = fns ++ fnsTF from rfl, List.all_append, h1, h2]
  all_goals rfl

/-- The valid calls are in the backend stages' scope. -/
theorem hscope3 : ∀ call, genericValid0 fns3 deployed call → SolarTV.Milestone.Uv2Erc20ATF.scope call := by
  rintro _ ⟨σ, -, f, hf, args, hlen, hargs, rfl⟩
  simp only [fns3, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have h := (Generic.callFacts fn_approve.sel (by decide) args hargs σ).selector
    simp only [SolarTV.Milestone.Uv2Erc20ATF.scope]
    rw [h]
    decide
  · have h := (Generic.callFacts fn_transfer.sel (by decide) args hargs σ).selector
    simp only [SolarTV.Milestone.Uv2Erc20ATF.scope]
    rw [h]
    decide
  · have h := (Generic.callFacts fn_transferFrom.sel (by decide) args hargs σ).selector
    simp only [SolarTV.Milestone.Uv2Erc20ATF.scope]
    rw [h]
    decide

/-- **approve, transfer and transferFrom, from SolidCore's source to the exact bytecode**:
equivalence, termination and the exported specs, under the named hypotheses. -/
theorem published (hsep : NestedSlotsSeparated [1, 4] [2])
    (hP : ∀ gas, SolidCore.Refinement.Solar.AssembleCallSeg.StaticRunner gas)
    (hQ : ∀ gas call, genericValid0 fns3 deployed call →
      SolidCore.Refinement.Solar.AssembleCallSeg.CalleesRun gas SolarTV.Export.UniswapV2ERC20.Ctx.code call) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Functional (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c SolarTV.Export.UniswapV2ERC20.Ctx.code
        (genericValid0 fns3 deployed) (fun _ _ => True) Post := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  refine ⟨c, hc, functional_ctx hdd (check3_ok hc) (base := SolarTV.Export.UniswapV2ERC20.Ctx.cx.base)
    (by decide) (genericValid0_inhabited fn_approve [fn_transfer, fn_transferFrom] deployed)
    (fun o => SolarTV.Milestone.Uv2Erc20ATF.uv2_erc20_atf_mir_to_evmir o) hscope3 ?_ ?_⟩
  · intro gas hg call hv
    obtain ⟨o, -, -, -, hok, hw⟩ :=
      SolarTV.Export.UniswapV2ERC20.Ctx.bytecode [] _ hP hQ gas hg call hv
    exact ⟨o, hok, hw⟩
  · exact ((meets_of_holdsFn (approve_holds hsep hc EndToEnd.idStep (fun _ _ _ => rfl))).and
      (meets_of_holdsFn (transfer_holds hsep hc EndToEnd.idStep (fun _ _ _ => rfl)))).and
      (meets_of_holdsFn (SolidCore.Spec.UniswapV2.ERC20TF.transferFrom_holds hsep hc EndToEndTF.idStep
        (fun _ _ _ => rfl)))

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.EndToEndAll.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

end SolidCore.Spec.UniswapV2.ERC20.EndToEndAll
