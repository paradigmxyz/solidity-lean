import Verify.Phase3.RecSource.Runs

/-!
# `total(n)` in SolidCore, from its source

`total`'s body runs to the tree `totalBr`: it reverts with empty data when `n > 64`, and otherwise
returns `n * (n + 1) / 2`, the call of `sum(n)` running by `sum_runs` (induction on the measure).
`runs` is then the generic dispatcher theorem (`runtime_run_clean`) on it: every call of
`total(n)` with no value runs, in SolidCore's runtime semantics, to that tree's observable.
-/

namespace Verify.Phase3.RecSource
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- `n * (n + 1) / 2` on the argument word. -/
def triW : WExpr := .bin .div (.bin .mul (.arg 0) (.bin .add (.arg 0) (.lit 1))) (.lit 2)

/-- `n <= 64`. -/
def le64 : WExpr := .un .iszero (.bin .gt (.arg 0) (.lit 64))

/-- **total's tree of leaves.** -/
def totalBr : Br := .ite le64 (.leaf (.returned S0 [triW] [])) (.leaf (.reverted .empty))

theorem e_req (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 (.requireStmt (.binary .le cn (.word 64)) none) S2 =
      some (.ite le64 (.leaf (.normal S2)) (.leaf (.reverted .empty))) := rfl

theorem e_argN (tbl : FunctionTable) :
    eraseStmt (envT tbl) 10 (.varDecl .uint256 "_ic_arg_0" (some cn)) S3.push =
      some (.leaf (.normal { S3 with scopes := [[("_ic_arg_0", .arg 0)], [("_sol_hoist_0", .lit 0)], [],
        [("n", .arg 0), ("_ret0", .lit 0)]] })) := rfl

theorem e_retH (tbl : FunctionTable) (t : Nat) :
    eraseStmt (envT tbl) 10 (.returnValues [.castOp .uintCleanup 256 (.var "_sol_hoist_0")]) (Sf t) =
      some (.leaf (.returned (Sf t) [.lit t] [])) := rfl

theorem triW_eval {ρ : Val} (h : (WExpr.arg 0).eval ρ ≤ 64) :
    triW.eval ρ = tri ((WExpr.arg 0).eval ρ) := by
  have hW := wordSize_gt
  generalize hv : (WExpr.arg 0).eval ρ = v at h
  simp only [triW, WExpr.eval] at hv ⊢
  rw [hv]
  have h1 : 1 % Generic.wordSize = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % Generic.wordSize = 2 := Nat.mod_eq_of_lt (by omega)
  have hv1 : (v + 1) % Generic.wordSize = v + 1 := Nat.mod_eq_of_lt (by omega)
  have hm : v * (v + 1) ≤ 64 * 65 := Nat.mul_le_mul h (by omega)
  have hlt : v * (v + 1) < Generic.wordSize := Nat.lt_of_le_of_lt hm (by omega)
  have hlt2 : v * (v + 1) / 2 < Generic.wordSize := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  simp only [BinOp.eval, tri, h1, h2, hv1, Nat.mod_mod, Nat.mod_eq_of_lt hlt,
    show (2 : Nat) ≠ 0 by decide, ↓reduceIte, Nat.mod_eq_of_lt hlt2]

set_option maxHeartbeats 4000000 in
/-- **total's body runs to `totalBr`**, at every fuel from 1045 on. -/
theorem total_runs {tbl : FunctionTable} (htbl : tbl.lookup? sumName = some sumFn) (fuel : Nat)
    (hfuel : 1045 ≤ fuel) : BodyRuns (envT tbl) fuel totalFn totalBr := by
  intro ρ ctx rt hrel
  change StmtRel ρ (envT tbl) ctx rt S0 at hrel
  change ∃ r, Stmt.eval fuel tbl ctx rt totalBody = _ ∧ _
  obtain ⟨j, rfl⟩ : ∃ j, fuel = j + 5 := ⟨fuel - 5, by omega⟩
  have hW := wordSize_gt
  -- n = n; skip
  obtain ⟨r1, h1, l1⟩ := run_e (e_assign tbl) hrel.pushScope (n := j + 4) (by omega)
  obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
  have hs := eval_skip (j + 3) tbl ctx rt1
  -- require(n <= 64);
  obtain ⟨r2, h2, l2⟩ := run_e (e_req tbl) hrel1.pushScope (n := j + 3) (by omega)
  unfold totalBr
  simp only [Br.eval] at l2 ⊢
  by_cases hle : le64.eval ρ = 0
  · -- n > 64: the require reverts with empty data
    simp only [hle, ↓reduceIte] at l2 ⊢
    cases r2 <;> simp only [LeafRel] at l2
    have hl := evalList_cons_stop (rest := [.varDecl .uint256 "_sol_hoist_0" none, callBlock cn,
      .returnValues [.castOp .uintCleanup 256 (.var "_sol_hoist_0")]]) h2 (fun _ h => by cases h)
    have hall := eval_block_of ((evalList_cons_normal h1).trans ((evalList_cons_normal hs).trans
      (evalList_cons_stop (rest := []) (eval_block_of hl) (fun _ h => by cases h))))
    exact ⟨_, hall, l2⟩
  simp only [hle, ↓reduceIte] at l2 ⊢
  obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
  have hv : (WExpr.arg 0).eval ρ ≤ 64 := by
    by_contra hc
    apply hle
    have hc' : 64 < (WExpr.arg 0).eval ρ := by omega
    have e : le64.eval ρ = UnOp.iszero.eval (BinOp.gt.eval ((WExpr.arg 0).eval ρ)
        (64 % Generic.wordSize) % Generic.wordSize) % Generic.wordSize := rfl
    rw [e]
    generalize (WExpr.arg 0).eval ρ = x at hc' ⊢
    simp [UnOp.eval, BinOp.eval, Nat.mod_eq_of_lt (show 64 < Generic.wordSize by omega), hc']
  set v := (WExpr.arg 0).eval ρ with hvdef
  have htv := tri_le v hv
  have ht : tri v < Generic.wordSize := by omega
  -- uint256 _sol_hoist_0;
  obtain ⟨r3, h3, l3⟩ := run_e (e_hoist tbl) hrel2 (n := j + 3) (by omega)
  obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
  -- uint256 _ic_arg_0 = n; uint256 _ret_sum_0;
  obtain ⟨r4, h4, l4⟩ := run_e (e_argN tbl) hrel3.pushScope (n := j + 2) (by omega)
  obtain ⟨rt4, rfl, hrel4⟩ := leaf_normal l4
  obtain ⟨r5, h5, l5⟩ := run_e (e_ret tbl (.arg 0)) hrel4 (n := j + 2) (by omega)
  obtain ⟨rt5, rfl, hrel5⟩ := leaf_normal l5
  -- _ret_sum_0 = sum(n), by the induction on the measure
  obtain ⟨rt6, h6, hrel6⟩ := call_runs (sc := (Sd (.arg 0) (tri v)).scopes) htbl hrel5 rfl rfl rfl rfl
    hvdef.symm rfl (sum_runs htbl ctx v hv j (by omega)) ht
  -- _sol_hoist_0 = _ret_sum_0;
  obtain ⟨r7, h7, l7⟩ := run_e (e_assignH tbl (.arg 0) (tri v)) hrel6 (n := j + 2) (by omega)
  obtain ⟨rt7, rfl, hrel7⟩ := leaf_normal l7
  have hcb := eval_block_of ((evalList_cons_normal h4).trans ((evalList_cons_normal h5).trans
    ((evalList_cons_normal h6).trans ((evalList_cons_normal h7).trans (evalList_nil _ _ _ _)))))
  have hcb' : Stmt.eval (j + 3) tbl ctx rt3 (callBlock cn) = .done (.ok (.normal rt7.popScope)) := hcb
  -- return _sol_hoist_0;
  obtain ⟨r8, h8, l8⟩ := run_e (e_retH tbl (tri v)) hrel7.popScope (n := j + 3) (by omega)
  obtain ⟨rt8, rfl, hrel8⟩ := leaf_returned l8
  have hl := (evalList_cons_normal h2).trans ((evalList_cons_normal h3).trans
    ((evalList_cons_normal hcb').trans (evalList_cons_stop (rest := []) h8 (fun _ h => by cases h))))
  have hall := eval_block_of ((evalList_cons_normal h1).trans ((evalList_cons_normal hs).trans
    (evalList_cons_stop (rest := []) (eval_block_of hl) (fun _ h => by cases h))))
  refine ⟨_, hall, ?_⟩
  refine ⟨hrel8.popScope.popScope, ?_⟩
  show [Value.word ((WExpr.lit (tri v)).eval ρ)] = [Value.word (triW.eval ρ)]
  rw [triW_eval hv, ← hvdef, show (WExpr.lit (tri v)).eval ρ = tri v from Nat.mod_eq_of_lt ht]

/-- info: 'Verify.Phase3.RecSource.total_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms total_runs

end Verify.Phase3.RecSource
