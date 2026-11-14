import Contracts.UniswapV2.ERC20.Slice.Mutants

/-!
# UniswapV2ERC20.transfer: the exported spec is not vacuous

solar-verify's exported spec (as `bundlePost`) rejects the return mutant's run of `call0` (success,
returning `false`): its `ensures` `returns true` fails. So the spec the unmutated contract meets on
every valid call (`meets_bundle`) rejects an observable a compiled program actually produces
(`nonVacuous_bundle`, `ret_refuted_bundle`).
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice SolidCore.Spec.UniswapV2.ERC20.Slice.Gen

/-- The state before `call0`. -/
def pre0 : State := ⟨slotValue σ0, Ghost.zero, 0⟩

theorem decodes0 : Decodes transfer_spec call0 [1, 0] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [show call0.calldata = Abi.calldata transferSel [1, 0] from rfl, words_calldata _ (by simp)]
  decide +kernel

theorem pre_call0 : Pre spec transfer_spec (ctxOf call0) pre0 call0 [1, 0] :=
  ⟨decodes0, rfl, by decide, by simp [Bundle.satAll, transfer_spec, Gen.spec,
    SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20],
    by simp [Bundle.satAll, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20]⟩

/-- **The exported spec rejects a success returning `false`** on `call0`. -/
theorem bundle_rejects_false {obs : Observable} (h1 : obs.success = true) (h2 : obs.output = be32 0) :
    ¬ bundlePost spec ctxOf idStep call0 obs := by
  intro hb
  have hp := hb transfer_spec (by rw [specs_eq]; exact List.mem_singleton_self _) [1, 0] pre0 pre_call0
  obtain ⟨rets, hdec, hens, -⟩ := hp.1 h1
  rw [h2, show words (be32 0) = [0] by decide +kernel] at hdec
  have hr : rets = [0] := by
    simp [transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20, decodeWords,
      Ty.ofWord] at hdec
    exact hdec.symm
  subst hr
  have := hens (.ret 0) (by simp [transfer_spec, Gen.spec, SolidCore.Spec.Export.UniswapV2ERC20Slice.UniswapV2ERC20])
  simp [Bundle.sat, eval, mkEnv, Env.cur, Env.bind] at this

/-- **The exported spec is not vacuous** on the valid calls with their premise. -/
theorem nonVacuous_bundle : ∃ call obs, ValidIn call ∧ ¬ bundlePost spec ctxOf idStep call obs :=
  ⟨call0, ⟨true, be32 0, [], slotValue σ0⟩, valid_call0, bundle_rejects_false rfl rfl⟩

/-- **The return mutant fails the exported spec**, by its run on `call0`. -/
theorem ret_refuted_bundle {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutRet.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (fun call => Valid Gen.MutRet.deployed call ∧ Scope call)
      (bundlePost spec ctxOf idStep) := fun h =>
  bundle_rejects_false ret_result.1 ret_result.2
    (h call0 ⟨valid0 _ coversRet, scope_call0⟩ _ (runRet hc))

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.ret_refuted_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ret_refuted_bundle

end SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants
