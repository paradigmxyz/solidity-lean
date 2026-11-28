import Verify.LoopSource.Equiv.From.Binding
import Verify.LoopSource.Equiv.LoopFrom
import Verify.LoopSource.Proof.LoopVC

/-!
# bump's loop from any caller, bound to solar-verify's obligations

`Verify.LoopSource.Proof.LoopVC` binds solar-verify's obligations for `bump`
(`Verify.LoopSource.RC.Counter.Obligations`, valid by `obs_valid`) to the source loop through the
loop-head map solar-verify emitted (`Verify.LoopSource.RC.Counter.Map`): its `init_vc`,
`consec_vc`, `decr_vc` and `post_vc` derive initiation, consecution, the measure's fall and the
exit, as facts about the header's words, from those obligations. The facts are about words only,
not about the caller, so they serve the symbolic-caller loop of `Verify.LoopSource.Equiv.From` as
they are: its header `headerS` differs from the default one only in its `caller` field.

`obl_vc` takes the loop's obligations (`ForObl`) from them, and `body_runs_vc` bump's body run from
the symbolic-caller first state (`BodyRunsFrom`), initiation from `init_vc`.

Not from solar-verify: the overflow guards of `count++` and `i++` (`hc1`, `hi1`), proved here from
the invariant and the precondition, since solar-verify outside `--strict` treats an overflow as a
reverting path rather than an obligation.
-/

namespace Verify.LoopSource.Equiv.From.VC
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Verify.LoopSource.Equiv.From Verify.LoopSource.Equiv.From.Binding
open Contracts.VerifyCounter.LoopVC (init_vc consec_vc decr_vc post_vc)

set_option maxHeartbeats 4000000 in
/-- **The loop's obligations hold**, consecution and termination from solar-verify's obligations. -/
theorem obl_vc (ev : List EventDecl) (tbl : FunctionTable) (ρ : Val) (ctx : Context) (hok : ρ.Ok)
    (hpre : ρ.store 0 + nOf ρ ≤ ρ.store 1) :
    ForObl 3 (env ev tbl) ctx cond post body headerS (P ρ) m (Q ρ (env ev tbl) ctx) c bb where
  cond_erase := rfl
  body_runs := stmtRuns_block1 (stmtRuns_incField 1 true rfl)
  exit := by
    rintro σ rt ⟨i, _, hiw, hcw, rfl, hi, rfl⟩ hrel hc0
    have hge : ¬ i < nOf ρ := fun hlt => by rw [c_eval ρ i hiw, if_pos hlt] at hc0; cases hc0
    -- the exit: solar-verify's obligation post_6
    have hie : i = nOf ρ := by
      have := post_vc _ _ _ i _ (hok.word 0) (hok.word 1) (nOf_lt ρ) hiw hcw hpre hi rfl hge
      omega
    refine ⟨rt, rfl, StmtRel.congr hrel hrel.hash hok (Facts.hold_nil _) ?_ ?_ rfl⟩
    · simp [headerS, exitS, frameOf, WExpr.eval, hval, Nat.mod_eq_of_lt hiw, hie, nOf]
    · intro k _
      have hie' : ρ.args.getD 0 0 % Generic.wordSize = i := hie.symm
      simp only [Writes.store, headerS, exitS, WExpr.eval, BinOp.eval, hval, List.getD_cons_succ,
        List.getD_cons_zero]
      by_cases hk0 : 0 % Generic.wordSize = k % Generic.wordSize <;> simp only [hk0, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (hok.word 0), hie', Nat.mod_mod]
  iter := by
    rintro σ ⟨i, _, hiw, hcw, rfl, hi, rfl⟩ hc
    have hn := nOf_lt ρ
    have hin : i < nOf ρ := by
      by_contra hge
      exact hc (by rw [c_eval ρ i hiw, if_neg hge])
    have hc1 : ρ.store 0 + i + 1 < Generic.wordSize := by have := hok.word 1; omega
    have hi1 : i + 1 < Generic.wordSize := by omega
    -- the body: count++, its overflow guard false
    have hbb : bb.eval (hval ρ i (ρ.store 0 + i)) = .normal SB := by
      have hbr : incFieldBr 0 0 32 headerS.push =
          guards [.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)]
            (.leaf (.normal { headerS.push with writes := [(.lit 0, .bin .add (.arg 2) (.lit 1))] })) := rfl
      have hg : ([WExpr.bin .lt (.bin .add (.arg 2) (.lit 1)) (.arg 2)].any
          (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0)) = false := by
        simp [WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hcw, Nat.mod_eq_of_lt hc1]
      rw [bb, Br.eval_mapS, hbr, guards_eval, hg]
      rfl
    rw [hbb]
    -- the update: i++, its overflow guard false
    refine ⟨incVarBr (.arg 1) L' SB, stmtRuns_incVar 2 true rfl rfl, ?_⟩
    have hg2 : (overflow .add (.arg 1) (.lit 1)).toList.any
        (fun g => g.eval (hval ρ i (ρ.store 0 + i)) != 0) = false := by
      simp [overflow, WExpr.eval, BinOp.eval, hval, Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
    simp only [incVarBr, guards_eval, hg2, Bool.false_eq_true, ↓reduceIte, Br.eval]
    -- back at the header with i + 1, the measure one lower: solar-verify's obligations
    -- consec_2, consec_3 and decr_4
    have hc1' : ρ.store 0 + (i + 1) < Generic.wordSize := by omega
    obtain ⟨hn1, -⟩ := consec_vc _ _ _ i _ (hok.word 0) (hok.word 1) hn hiw hcw hpre hi rfl hin
    refine ⟨hval ρ (i + 1) (ρ.store 0 + (i + 1)),
      ⟨i + 1, ρ.store 0 + (i + 1), hi1, hc1', rfl, hn1, rfl⟩, ?_, ?_⟩
    · obtain ⟨a0, a1, -⟩ := hval_args ρ i (ρ.store 0 + i) hiw hcw
      obtain ⟨b0, b1, -⟩ := hval_args ρ (i + 1) _ hi1 hc1'
      simp only [m, a0, a1, b0, b1]
      exact decr_vc _ _ _ i _ (hok.word 0) (hok.word 1) hn hiw hcw hpre hi rfl hin
    · intro rp hl2
      refine StmtRel.congr hl2 hl2.hash hok (Facts.hold_nil _) ?_ ?_ rfl
      · simp [SB, L', headerS, SymState.pop, SymState.push, frameOf, WExpr.eval, BinOp.eval, hval,
          Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hi1]
      · intro k _
        simp only [Writes.store, SB, SymState.pop, SymState.push, headerS, WExpr.eval, BinOp.eval,
          hval, List.getD_cons_succ, List.getD_cons_zero]
        split_ifs
        · rw [Nat.mod_eq_of_lt hcw, show 1 % Generic.wordSize = 1 by decide, Nat.mod_mod, ← Nat.add_assoc]
        · rfl

set_option maxHeartbeats 4000000 in
/-- **bump's body runs to `bumpBr`** from the symbolic-caller first state, at every fuel from
`2 ^ 256 + 8` on: the statements before the loop as their erasure, the loop by the generic bridge
from `obl_vc`, initiation from solar-verify's `init_vc`. -/
theorem body_runs_vc (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef)
    (hbody : fn.body = bumpBody) (hinit : initFrom fn = S0) (fuel : Nat)
    (hfuel : 2 ^ 256 + 8 ≤ fuel) : BodyRunsFrom (env ev tbl) fuel fn bumpBr := by
  intro ρ ctx rt hrel
  rw [hinit] at hrel
  rw [hbody]
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  have hok : ρ.Ok := hrel.ok
  set E := env ev tbl with hE
  -- n = n
  obtain ⟨r1, h1, l1⟩ := eval_stmt ρ E ctx 10 s1 S0.push _ (e1 ev tbl) rt.pushScope hrel.pushScope
  obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
  have h1' := eval_mono (by omega : 10 ≤ f + 3) h1
  -- require(count + n <= limit, "over")
  obtain ⟨r2, h2, l2⟩ := eval_stmt ρ E ctx 10 s2 S0.push.push _ (e2 ev tbl) rt1.pushScope
    hrel1.pushScope
  have h2' := eval_mono (by omega : 10 ≤ f + 2) h2
  unfold bumpBr
  simp only [guards_eval, Br.eval] at l2 ⊢
  split_ifs at l2 ⊢ with hg hv
  -- the two reverting ends: the overflow guard and the failed require
  iterate 2
    cases r2 <;> simp only [LeafRel] at l2
    have hl2 := evalList_cons_stop (rest := [.block [s3, loop]]) h2' (fun _ h => by cases h)
    have hl1 := evalList_cons_stop (rest := []) (eval_block_of hl2) (fun _ h => by cases h)
    exact ⟨_, eval_block_of ((evalList_cons_normal h1').trans hl1), l2⟩
  obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
  have h0 := hok.word 0
  have hpre := require_passed ρ hok hg hv
  -- uint256 i = 0
  obtain ⟨r3, h3, l3⟩ := eval_stmt ρ E ctx 10 s3 S0.push.push.push _ (e3 ev tbl) rt2.pushScope
    hrel2.pushScope
  obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
  have h3' := eval_mono (by omega : 10 ≤ f + 1) h3
  -- initiation: the header at i = 0
  have hrelh : StmtRel (hval ρ 0 (ρ.store 0 + 0)) E ctx rt3.pushScope headerS := by
    refine StmtRel.congr hrel3.pushScope hrel3.hash hok (Facts.hold_nil _) ?_ ?_ rfl
    · simp [SymState.push, S0, headerS, frameOf, WExpr.eval, hval]
    · intro k hk
      simp only [Writes.store, SymState.push, S0, headerS]
      split_ifs with hk0
      · simp only [WExpr.eval, hval, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero] at hk0 ⊢
        rw [Nat.mod_eq_of_lt hk] at hk0
        rw [← hk0, Nat.mod_eq_of_lt h0, Nat.zero_mod]
      · rfl
  have hskip : Stmt.eval 1 E.tbl ctx rt3.pushScope .skip = .done (.ok (.normal rt3.pushScope)) := by
    rw [Stmt.eval]; rfl
  have hm0 : m (hval ρ 0 (ρ.store 0 + 0)) < 2 ^ 256 := by
    obtain ⟨z0, z1, -⟩ := hval_args ρ 0 (ρ.store 0 + 0) (by decide) (by omega)
    simp only [m, z0, z1]
    have := nOf_lt ρ
    omega
  -- the loop, by the generic bridge
  obtain ⟨r, hr, hq⟩ := forLoop_of_erased (obl_vc ev tbl ρ ctx hok hpre) hskip
    ⟨0, ρ.store 0 + 0, by decide, by omega, rfl,
      init_vc _ _ _ h0 (hok.word 1) (nOf_lt ρ) hpre⟩ hrelh (f + 1) (by omega) (by omega)
  obtain ⟨rtx, rfl, hrelx⟩ := hq
  have hr' : Stmt.eval (f + 1) E.tbl ctx rt3 loop = .done (.ok (.normal rtx.popScope)) := hr
  -- the blocks around the loop end normally
  have hb3 := eval_block_of (by
    rw [evalList_cons_normal h3', evalList_cons_normal hr', evalList_nil] :
    Stmt.evalList (f + 1) E.tbl ctx rt2.pushScope [s3, loop] = .done (.ok (.normal rtx.popScope)))
  have hb2 := eval_block_of (by
    rw [evalList_cons_normal h2', evalList_cons_normal hb3, evalList_nil] :
    Stmt.evalList (f + 2) E.tbl ctx rt1.pushScope [s2, .block [s3, loop]] =
      .done (.ok (.normal rtx.popScope.popScope)))
  have hl1 : Stmt.evalList (f + 3) E.tbl ctx rt.pushScope [s1, .block [s2, .block [s3, loop]]] =
      .done (.ok (.normal rtx.popScope.popScope.popScope)) := by
    rw [evalList_cons_normal h1', evalList_cons_normal hb2, evalList_nil]
  exact ⟨_, eval_block_of hl1, hrelx.popScope.popScope.popScope.popScope⟩

/-- info: 'Verify.LoopSource.Equiv.From.VC.body_runs_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms body_runs_vc

end Verify.LoopSource.Equiv.From.VC
