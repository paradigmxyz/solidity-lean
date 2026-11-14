import Contracts.UniswapV2.ERC20.Slice.Bytes
import Contracts.UniswapV2.ERC20.Slice.Gen.MutLog.Tree
import Contracts.UniswapV2.ERC20.Slice.Gen.MutRet.Tree

/-!
# UniswapV2ERC20.transfer: semantic mutants of the port, refused by execution

Each mutant is one text edit of the pinned port (scripts/verify/uniswap-v2/transfer-mutants.txt),
compiled by the same frontend and checked by the kernel (`Gen/Mut<M>/Core.lean`, `contract_ok`),
its `transfer` erased by the same generic source stage (`Gen/Mut<M>/Tree.lean`,
`transfer_erase_eq`, `deploy_eq`). The refutations run SolidCore's checked mutant on one valid call
(`run<M>`, `source_run`) and evaluate the result: no formula is checked on a hand-written state.

* `Log` (`emit Transfer(to, from, value)`): `transfer(1, 0)` from `σ0` succeeds with the log's
  addresses swapped; `SeqPost` and `TargetPost` refuse it (`log_refuted_seq`,
  `log_refuted_target`). solar-verify's exported spec says nothing of logs, so it does not.
* `Ret` (`return false`): the same call returns `false`; refused by `SeqPost`, `TargetPost` and
  the exported spec (`returns true`; `ret_refuted_bundle`).
* `Debit` (`balanceOf[from] = balanceOf[from].sub(value).add(value)`: the debit undone):
  `transfer(1, 2)` from a balance of 5 succeeds and leaves it at 5; `TargetPost` and `SeqPost`
  refuse it (`debit_refuted_target`, `debit_refuted_seq`, MutantsDebit.lean).

The unmutated contract meets all three on the same call (`meets_seq`, `meets_target`,
`meets_bundle`), so each refusal is the mutation's.
-/

namespace SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Spec SolidCore.Refinement.Shapes
open SolidCore.Spec.UniswapV2.ERC20.Slice

theorem slotValue_σ0 : slotValue σ0 = fun _ => 0 := by
  funext n; simp [slotValue, σ0]

theorem valid0 (s : List (Nat × Nat)) (hs : Generic.Covers s σ0) : Valid s call0 :=
  ⟨σ0, 1, 0, hs, by decide, by decide, rfl⟩

/-- \`σ0\` writes every slot of a constructor storage that writes only slot 3. -/
theorem covers_3 {s : List (Nat × Nat)} (h : ∀ kv ∈ s, kv.1 = 3) : Generic.Covers s σ0 := by
  intro kv hkv
  exact ⟨(3, 0), by simp [σ0], by rw [h kv hkv]⟩

theorem coversLog : Generic.Covers Gen.MutLog.deployed σ0 := covers_3 (by simp [Gen.MutLog.deployed])
theorem coversRet : Generic.Covers Gen.MutRet.deployed σ0 := covers_3 (by simp [Gen.MutRet.deployed])

/-! ## Log -/

section Log
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen.MutLog in
/-- SolidCore's run of `call0` on the mutant is its erased tree's result. -/
theorem runLog {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutLog.contract? = .ok c) :
    (solidCore fuel).run c call0 = some (transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep
  have hmap := transfer_erase_eq
  simp only [transfer_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact source_run hd covers_σ0 (by decide) hf hT [1, 0] (by simp [hlen]) (by simp)
end Log

/-! ## Ret -/

section Ret
open SolidCore.Spec.UniswapV2.ERC20.Slice.Gen.MutRet in
/-- SolidCore's run of `call0` on the mutant is its erased tree's result. -/
theorem runRet {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutRet.contract? = .ok c) :
    (solidCore fuel).run c call0 = some (transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs := by
  have hdep := deploy_eq
  simp only [deploy?, hc] at hdep
  obtain ⟨d, hd⟩ := Wide.deployedAt_of hdep
  have hmap := transfer_erase_eq
  simp only [transfer_erase?, hc, Option.map_eq_some_iff, Prod.mk.injEq] at hmap
  obtain ⟨f, hf, hlen, hT⟩ := hmap
  exact source_run hd covers_σ0 (by decide) hf hT [1, 0] (by simp [hlen]) (by simp)
end Ret

/-- The log mutant's result on `call0`: success, with `Transfer(1, caller, 0)`. -/
theorem log_result :
    (Gen.MutLog.transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs.success = true ∧
      (Gen.MutLog.transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs.logs ≠ [transferLog caller 1 0] := by
  simp only [Res.obs, slotValue_σ0]
  generalize solHash = H
  simp [Gen.MutLog.transfer_tree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Log.eval, transferLog,
    caller, Generic.callerWord, Generic.wordSize]

/-- The return mutant's result on `call0`: success, returning `false`. -/
theorem ret_result :
    (Gen.MutRet.transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs.success = true ∧
      (Gen.MutRet.transfer_tree.eval ⟨[1, 0], slotValue σ0, solHash⟩).obs.output = be32 0 := by
  simp only [Res.obs, slotValue_σ0]
  generalize solHash = H
  simp [Gen.MutRet.transfer_tree, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, OByte.eval, be32,
    Generic.wordSize]

theorem be32_ne : be32 0 ≠ be32 1 := by decide

/-- **The log mutant fails `SeqPost`**, by its run on `call0`. -/
theorem log_refuted_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutLog.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (Valid Gen.MutLog.deployed) SeqPost := by
  intro h
  have hp := h call0 (valid0 _ coversLog) _ (runLog hc) σ0 1 0 rfl (by decide) (by decide)
  exact log_result.2 (hp.2.1 log_result.1).2.1

/-- **The log mutant fails `TargetPost`** on a call whose footprint premise holds. -/
theorem log_refuted_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutLog.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (fun call => Valid Gen.MutLog.deployed call ∧ Scope call) TargetPost := by
  intro h
  have hp := h call0 ⟨valid0 _ coversLog, scope_call0⟩ _ (runLog hc) σ0 1 0 rfl (by decide) (by decide)
  exact log_result.2 (hp.2.2.1 log_result.1).1

/-- **The return mutant fails `SeqPost`.** -/
theorem ret_refuted_seq {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutRet.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (Valid Gen.MutRet.deployed) SeqPost := by
  intro h
  have hp := h call0 (valid0 _ coversRet) _ (runRet hc) σ0 1 0 rfl (by decide) (by decide)
  exact be32_ne (ret_result.2.symm.trans (hp.2.1 ret_result.1).2.2)

/-- **The return mutant fails `TargetPost`.** -/
theorem ret_refuted_target {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : SolidCore.Verify.VC.UniswapV2ERC20MutRet.contract? = .ok c) :
    ¬ Meets (solidCore fuel) c (fun call => Valid Gen.MutRet.deployed call ∧ Scope call) TargetPost := by
  intro h
  have hp := h call0 ⟨valid0 _ coversRet, scope_call0⟩ _ (runRet hc) σ0 1 0 rfl (by decide) (by decide)
  exact be32_ne (ret_result.2.symm.trans (hp.2.2.1 ret_result.1).2.1)

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.log_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms log_refuted_target

/-- info: 'SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants.ret_refuted_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ret_refuted_target


end SolidCore.Spec.UniswapV2.ERC20.Slice.Mutants
