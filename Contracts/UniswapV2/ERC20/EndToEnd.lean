import Verify.ShapeCtx
import Contracts.UniswapV2.ERC20.Lowering
import uv2_erc20.ProofsAT.Stages
import uv2_erc20.Ctx

/-!
# UniswapV2ERC20's approve and transfer: SolidCore's source to solar's exact runtime bytecode

`published`: `Shapes.Functional` (equivalence, termination and the specification; no gas bound)
of SolidCore's checked `UniswapV2ERC20` (the kernel's type check and translation of the port,
`Contracts.UniswapV2.ERC20.Core`) and the exact runtime bytecode solar emitted for it
(`SolarTV.Export.UniswapV2ERC20.bytecode`, 2187 bytes, -Ogas, osaka), on the valid calls
`genericValid0 fns deployed`: `approve(address,uint256)` and `transfer(address,uint256)` on any
argument words below `2 ^ 256`, with no value, from the stage's caller, from any storage that writes
the slot the constructor wrote (`DOMAIN_SEPARATOR`).

It composes, by `Shapes.functional_ctx` alone:

* the generic source stage, `check_ok` (`Generic.check` of stage0 for both functions);
* solar-tv's backend stages from stage0 to the final EVM IR `evm16` under every oracle
  (`SolarTV.Milestone.Uv2Erc20AT.uv2_erc20_at_mir_to_evmir`, on every call whose selector is none
  of the eleven other external functions');
* the context checker's per-run theorem on the exact bytecode
  (`SolarTV.Export.UniswapV2ERC20.Ctx.bytecode`, `assembly_of_checkXB_norm`: the whole runtime,
  permit's STATICCALL to `ecrecover` included, under calling contexts);
* solar-verify's exported specs of approve and transfer (`approve_holds`, `transfer_holds`), with
  the identity ghost step (the spec moves its ghosts only in `_mint` and `_burn`).

Named hypotheses, all in the statement:

* `NestedSlotsSeparated [1, 4] [2]`: keccak256 injective with images at least `2 ^ 128` on the
  slots of `balanceOf[a]`, `nonces[a]` and `allowance[o][s]`; used by the specification only;
* `AssembleCallSeg.StaticRunner` at every gas (a static message that succeeds ends with no log, a
  callee's output has fewer than `2 ^ 256` bytes) and `AssembleCallSeg.CalleesRun` on the valid
  calls: the context checker's hypotheses on the message runner, used by equivalence only.

Not covered: resources (the context checker proves no gas bound, so this is not
`Shapes.Certified`); `transferFrom`, `permit`, the getters and the constructor (only through the
storage it leaves, `deploy_eq`); callers other than the stage's.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.EndToEnd

open SolidCore.Spec SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Spec.UniswapV2.ERC20

/-- The exact runtime bytecode. -/
abbrev code : ByteArray := SolarTV.Export.UniswapV2ERC20.Ctx.code

/-- The identity ghost step: approve and transfer leave the spec's ghosts alone. -/
def idStep : GhostStep := fun _ g => g

/-- The specification: approve's and transfer's exported specs of every result on their calls. -/
def Post (call : SolarTV.Call) (obs : SolarTV.Observable) : Prop :=
  holdsPost spec ctxOf idStep approve_spec (SolidCore.Verify.VC.stageScope fn_approve deployed) call obs ∧
    holdsPost spec ctxOf idStep transfer_spec (SolidCore.Verify.VC.stageScope fn_transfer deployed) call obs

/-- The valid calls are in the backend stages' scope: their selector is approve's or transfer's. -/
theorem hscope : ∀ call, genericValid0 fns deployed call → SolarTV.Milestone.Uv2Erc20AT.scope call := by
  rintro _ ⟨σ, -, f, hf, args, hlen, hargs, rfl⟩
  simp only [fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have h := (Generic.callFacts fn_approve.sel (by decide) args hargs σ).selector
    simp only [SolarTV.Milestone.Uv2Erc20AT.scope]
    rw [h]
    decide
  · have h := (Generic.callFacts fn_transfer.sel (by decide) args hargs σ).selector
    simp only [SolarTV.Milestone.Uv2Erc20AT.scope]
    rw [h]
    decide

/-- **approve and transfer, from SolidCore's source to the exact bytecode**: equivalence,
termination and the exported specs, under the named hypotheses. -/
theorem published (hsep : NestedSlotsSeparated [1, 4] [2])
    (hP : ∀ gas, SolidCore.Refinement.Solar.AssembleCallSeg.StaticRunner gas)
    (hQ : ∀ gas call, genericValid0 fns deployed call →
      SolidCore.Refinement.Solar.AssembleCallSeg.CalleesRun gas code call) :
    ∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Functional (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c code (genericValid0 fns deployed)
        (fun _ _ => True) Post := by
  obtain ⟨c, hc⟩ := SolidCore.Verify.VC.UniswapV2ERC20.contract_ok
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  refine ⟨c, hc, functional_ctx hdd (check_ok hc) (base := SolarTV.Export.UniswapV2ERC20.Ctx.cx.base)
    (by decide) (genericValid0_inhabited fn_approve [fn_transfer] deployed)
    (fun o => SolarTV.Milestone.Uv2Erc20AT.uv2_erc20_at_mir_to_evmir o) hscope ?_ ?_⟩
  · intro gas hg call hv
    obtain ⟨o, -, -, -, hok, hw⟩ :=
      SolarTV.Export.UniswapV2ERC20.Ctx.bytecode [] _ hP hQ gas hg call hv
    exact ⟨o, hok, hw⟩
  · exact (meets_of_holdsFn (approve_holds hsep hc idStep (fun _ _ _ => rfl))).and
      (meets_of_holdsFn (transfer_holds hsep hc idStep (fun _ _ _ => rfl)))

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.EndToEnd.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

end SolidCore.Spec.UniswapV2.ERC20.EndToEnd
