import SolidCore.Refinement.Generic.LoopErr
import Contracts.VerifyCounter.SourceMutantShape
import Contracts.VerifyCounter.ShapeSource

/-!
# A negative control: bump without its loop's update does not terminate

`SourceMutantAst.lean` is `Counter`'s solc AST with bump's loop update `i++` and its body
`count++` removed: `for (uint256 i = 0; i < n;) {}`. The kernel checks (`shapeM_eq`) that the type
checker accepts it, with the same storage fields and no events, and that its `bump` is `bumpFnM`,
whose loop is `loopM`.

* `body_err`: from every runtime related to bump's first symbolic state, on every call whose
  `require` passes and whose `n` is at least 1, the body **fails** at every fuel from 14 on (out of
  fuel): the loop's condition always holds and nothing changes (`forLoop_err`).
* `never`: the call `bump(1)` from the storage with `count = 0` and `limit = 1` has **no result**
  in `solidCoreRuntime fuel` at any fuel from 14 on (`runtime_run_err`).
* `not_terminates`, `not_certified`: so the mutant fails the termination obligation of the
  published shape on `bump`'s valid calls, whatever statuses it allows, and never reaches the
  strongest status (`Shapes.Certified`), whatever bytecode, specification and gas bound are named.
-/

namespace Contracts.VerifyCounter.Mutant
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source

theorem eval_zero_err (tbl : FunctionTable) (ctx : Context) (rt : Runtime) (st : Stmt) :
    Stmt.eval 0 tbl ctx rt st = .done (.error .outOfFuel) := by
  rw [Stmt.eval]; rfl

set_option maxHeartbeats 2000000 in
/-- **The mutant's body fails at every fuel from 14 on**, on a call whose `require` passes and
whose `n` is at least 1. -/
theorem body_err (ev : List EventDecl) (tbl : FunctionTable) (fn : FunctionDef)
    (hbody : fn.body = bumpBodyM) (fuel : Nat) (hfuel : 14 ≤ fuel)
    (ρ : Val) (ctx : Context) (rt : Runtime) (hrel : StmtRel ρ (env ev tbl) ctx rt S0)
    (hg : ¬([ovf].any (fun g => g.eval ρ != 0) = true)) (hv : ¬le.eval ρ = 0) (hn1 : 0 < nOf ρ) :
    ∃ e, Stmt.eval fuel tbl ctx rt fn.body = .done (.error e) := by
  rw [hbody]
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  have hok : ρ.Ok := hrel.ok
  set E := env ev tbl with hE
  show ∃ e, Stmt.eval (f + 4) E.tbl ctx rt bumpBodyM = .done (.error e)
  -- n = n
  obtain ⟨r1, h1, l1⟩ := eval_stmt ρ E ctx 10 s1 S0.push _ (e1 ev tbl) rt.pushScope hrel.pushScope
  obtain ⟨rt1, rfl, hrel1⟩ := leaf_normal l1
  have h1' := eval_mono (by omega : 10 ≤ f + 3) h1
  -- require(count + n <= limit, "over") passes
  obtain ⟨r2, h2, l2⟩ := eval_stmt ρ E ctx 10 s2 S0.push.push _ (e2 ev tbl) rt1.pushScope
    hrel1.pushScope
  have h2' := eval_mono (by omega : 10 ≤ f + 2) h2
  rw [guards_eval, if_neg hg] at l2
  simp only [Br.eval, if_neg hv] at l2
  obtain ⟨rt2, rfl, hrel2⟩ := leaf_normal l2
  have h0 := hok.word 0
  have hn := nOf_lt ρ
  -- uint256 i = 0
  obtain ⟨r3, h3, l3⟩ := eval_stmt ρ E ctx 10 s3 S0.push.push.push _ (e3 ev tbl) rt2.pushScope
    hrel2.pushScope
  obtain ⟨rt3, rfl, hrel3⟩ := leaf_normal l3
  have h3' := eval_mono (by omega : 10 ≤ f + 1) h3
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
  -- the loop: its condition always holds and nothing changes
  have hloop : ∀ g, ∃ e, Stmt.eval g E.tbl ctx rt3 loopM = .done (.error e) := by
    refine forLoop_err (fun rt => StmtRel (hval ρ 0 (ρ.store 0 + 0)) E ctx rt headerS) ?_ ?_
    · intro rt h
      have hcond : eraseExpr E.fields headerS cond = some ([], .bin .lt (.arg 1) (.arg 0)) := rfl
      have hev := eval_eq _ E.fields ctx rt headerS h.expr hcond
      refine ⟨1, rt, ?_, by decide, ?_⟩
      · have hval1 : (WExpr.bin .lt (.arg 1) (.arg 0)).eval (hval ρ 0 (ρ.store 0 + 0)) = 1 := by
          simp only [WExpr.eval, BinOp.eval, hval, List.getD_cons_succ, List.getD_cons_zero,
            Nat.zero_mod]
          have : 0 < ρ.args.getD 0 0 % Generic.wordSize := hn1
          rw [if_pos this]
          decide
        rw [hev, caught_exprResult]
        simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, hval1]
      · intro g
        cases g with
        | zero => exact Or.inl ⟨_, eval_zero_err _ _ _ _⟩
        | succ g =>
          refine Or.inr ⟨rt.pushScope.popScope, ?_, ?_⟩
          · rw [eval_block_of (evalList_nil g E.tbl ctx rt.pushScope)]
            rfl
          · refine Or.inr ⟨rt.pushScope.popScope, ?_, h.pushScope.popScope⟩
            rw [Stmt.eval]; rfl
    · intro g
      cases g with
      | zero => exact Or.inl ⟨_, eval_zero_err _ _ _ _⟩
      | succ g =>
        refine Or.inr ⟨rt3.pushScope, ?_, hrelh⟩
        rw [Stmt.eval]; rfl
  obtain ⟨e, he⟩ := hloop (f + 1)
  have hl3 : Stmt.evalList (f + 1) E.tbl ctx rt2.pushScope [s3, loopM] = .done (.error e) := by
    rw [evalList_cons_normal h3', evalList_cons_err he]
  have hl2 : Stmt.evalList (f + 2) E.tbl ctx rt1.pushScope [s2, .block [s3, loopM]] =
      .done (.error e) := by
    rw [evalList_cons_normal h2', evalList_cons_err (eval_block_err hl3)]
  have hl1 : Stmt.evalList (f + 3) E.tbl ctx rt.pushScope [s1, .block [s2, .block [s3, loopM]]] =
      .done (.error e) := by
    rw [evalList_cons_normal h1', evalList_cons_err (eval_block_err hl2)]
  exact ⟨e, eval_block_err hl1⟩

/-- The call `bump(1)` from `count = 0`, `limit = 1`: its `require` passes. -/
def badCall : SolarTV.Call := bumpCall [(1, 1)] 1

/-- **The mutant has no result on `bump(1)`**, at every fuel from 14 on. -/
theorem never {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contractM? = .ok c)
    (fuel : Nat) (hfuel : 14 ≤ fuel) : runtimeRun fuel c badCall = none := by
  obtain ⟨hf, hev, hfind⟩ := shapeM_of hc
  have hw : widthsOf bumpFnM.params bumpFnM.paramAbiCleanups = some [256] := rfl
  have hargs : ∀ x ∈ [1], x < 2 ^ 256 := by simp
  have hclean : argsClean [256] [1] = true := by decide
  have hdec := decode_args hw [1] rfl hargs
  rw [if_pos hclean] at hdec
  have hE : ({ envOf c.core with facts := argFacts [256] 0 } : EraseEnv) =
      env c.core.eventDecls c.core.table := by
    simp only [envOf, env, hf]
    rfl
  refine runtime_run_err (by decide) hfind hw rfl [1] rfl hargs hclean hdec ?_
  intro ctx rt hrel
  rw [hE] at hrel
  exact body_err _ _ bumpFnM rfl fuel hfuel _ ctx rt hrel (by decide) (by decide) (by decide)

/-- **The mutant fails the termination obligation** on bump's valid calls, at every fuel from 14
on (the statement's `fuel` among them), whatever statuses it allows. -/
theorem not_terminates : ∃ c, contractM? = .ok c ∧ ∀ fuel, 14 ≤ fuel →
    ∀ Allowed, ¬ Shapes.Terminates (solidCoreRuntime fuel) c BumpCall Allowed := by
  obtain ⟨c, hc⟩ := contractM_ok
  exact ⟨c, hc, fun fuel hf Allowed =>
    Shapes.not_terminates_of_none ⟨[(1, 1)], 1, by decide, rfl⟩ (never hc fuel hf)⟩

/-- **The mutant never reaches the strongest status** on the published valid calls, whatever
bytecode, statuses, specification and gas bound are named. -/
theorem not_certified : ∃ c, contractM? = .ok c ∧ ∀ (code : ByteArray) Allowed Post G,
    ¬ Shapes.Certified (solidCoreRuntime fuel) c code ShapeSource.ValidS Allowed Post G := by
  obtain ⟨c, hc⟩ := contractM_ok
  refine ⟨c, hc, fun code Allowed Post G h => ?_⟩
  exact Shapes.not_terminates_of_none (Valid := ShapeSource.ValidS) (Allowed := Allowed)
    ⟨[(1, 1)], 1, by decide, rfl⟩ (never hc fuel (by unfold fuel; omega)) h.terminates

/-- info: 'Contracts.VerifyCounter.Mutant.not_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_certified

/-- info: 'Contracts.VerifyCounter.Mutant.not_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_terminates

end Contracts.VerifyCounter.Mutant
