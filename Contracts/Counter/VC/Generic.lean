import Contracts.Counter.VC.Inc
import Verify.VC.Obligations

/-!
# `Counter.inc` through the generic theorem

`inc_triple` again, now as an instance of `triple_of_binds`: the only proof about `inc` is the
binding `inc_binds`, which speaks of the erased tree `incTree` and solar-verify's obligation alone
(no SolidCore run, no fuel, no ABI); `triple_of_binds` supplies the rest for every function the
generic source stage erases. The obligation `incHyps ⟹ incGoal` is the one `inc_check` finds in
solar-verify's script, and it is valid by solar-verify's own encoding (`inc_obs_valid`), so the
theorem takes no verdict.
-/

namespace SolidCore.Verify.VC.Counter

open SolidCore.Verify SolidCore.Verify.VC SolidCore.Refinement SolidCore.Refinement.Abi
open SolidCore.Refinement.Generic SolidCore.Solidity

/-- `inc`'s postcondition of its argument words, its storage and its observable. -/
def incP (args : List Nat) (s : Storage) (o : SolarTV.Observable) : Prop :=
  let d := args.getD 0 0
  (o.success = true ↔ s 0 + d < 2 ^ 256) ∧
    (o.success = true → o.storage 0 = s 0 + d ∧ ∀ k, k % 2 ^ 256 ≠ 0 → o.storage k = s k)

/-- solar-verify's obligation for `inc`'s clause holds everywhere. -/
theorem inc_obs_valid : ObsValid [(incHyps, incGoal)] := by
  intro o ho σ _
  simp only [List.mem_singleton] at ho
  subst ho
  simp [incGoal, incEff, Ob.add, Ob.eq, Ob.x, Ob.d, Tm.Holds, Tm.eval, Tm.evalList, applyOp, Value.select, Value.store,
    Value.toProp, Value.eq]

/-- The binding of `inc`'s erased tree to solar-verify's obligation. -/
theorem inc_binds :
    Binds fnInc incTree [(incHyps, incGoal)] (fun args s => incEnv (args.getD 0 0) s) incP := by
  intro args s hl hargs hs _
  obtain ⟨d, rfl⟩ : ∃ d, args = [d] := by
    match args, hl with
    | [d], _ => exact ⟨d, rfl⟩
  have hd : d < 2 ^ 256 := hargs d (List.mem_singleton_self d)
  obtain ⟨hiff, hok⟩ := inc_binding s hs d hd
  have hguard := incHyps_iff d s hd (hs 0)
  simp only [incP, Res.obs, List.getD_cons_zero]
  refine ⟨hiff.trans hguard, fun hsucc => ?_⟩
  obtain ⟨h0, hk⟩ := hok hsucc
  rw [incEff_eval] at h0
  exact ⟨by omega, hk⟩

/-- `inc_triple`, from the generic theorem and the binding. -/
theorem inc_triple_of_binds {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Triple fuel c (stageScope fnInc []) (fun _ => True) incPost := by
  have hshape := incShape_eq
  simp only [incShape?, hc, Option.some.injEq, Prod.mk.injEq] at hshape
  obtain ⟨hdep, hmap⟩ := hshape
  obtain ⟨dd, hdd⟩ := Wide.deployedAt_of hdep
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact triple_of_binds (fn := fnInc) hdd (by decide) hf hlen hT inc_obs_valid inc_binds

/-- info: 'SolidCore.Verify.VC.Counter.inc_triple_of_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inc_triple_of_binds

end SolidCore.Verify.VC.Counter
