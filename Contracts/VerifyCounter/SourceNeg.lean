import Contracts.VerifyCounter.SourceLoop

/-!
# Negative controls of bump's source certificate

* `growing_rejected`: the certificate of `SourceLoop.certWith` with the measure `i` (read off the
  runtime as `rank` reads `n - i`) is refused: its one remaining obligation, that the measure falls
  on an iteration, is `i + 1 < i`, which `omega` refutes at once; `fail_if_success` makes this file
  build only while that certificate is rejected. The same script with `n - i` is `SourceLoop.cert`.
* `missing_update_never`: the loop with its update `i++` dropped and an empty body,
  `for (; i < n;) {}`, from every header state with `i < n`, finishes at **no** fuel
  (`evalFor_never`): no ranking certificate exists for it and no fuel ends it. (Dropping only
  `i++` and keeping `count++` does end, by `count++`'s checked overflow, with `Panic(0x11)` on a call
  whose `require` passed: a revert the specification does not allow; not proved here.)
-/

namespace Contracts.VerifyCounter.Source
open SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop

/-- The measure `i`, read off the runtime: it grows. -/
def growing (rt : Runtime) : Nat :=
  match rt.lookupLocal? "i" with
  | some (.word v) => v
  | _ => 0

theorem growing_of {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {i c : Nat}
    (h : StmtRel (hval ρ i c) E ctx rt headerS) (hi : i < wordSize) : growing rt = i := by
  have := h.expr.locals "i" (.arg 1) rfl
  simp only [growing, this, WExpr.eval, hval, List.getD_cons_succ, List.getD_cons_zero,
    Nat.mod_eq_of_lt hi]

theorem growing_rejected : True := by
  fail_if_success
    have : ∀ ρ E ctx (hc : countOk E) (hf : E.facts = []) (hp : ρ.store 0 + nOf ρ ≤ ρ.store 1),
        ForCert 3 E.tbl ctx cond post body (Inv ρ E ctx) growing (Q ρ E ctx) :=
      fun ρ E ctx hc hf hp => certWith ρ E ctx hc hf hp growing fun i _ _ hin h h' => by
        have hn := nOf_lt ρ
        rw [growing_of h' (by omega), growing_of h (by omega)]
        omega
  trivial

set_option maxHeartbeats 2000000 in
/-- **Without its update the loop finishes at no fuel.** -/
theorem missing_update_never (ρ : Val) (E : EraseEnv) (ctx : Context) (i : Nat)
    (hi : i < nOf ρ) (rt : Runtime) (hrel : StmtRel (hval ρ i (ρ.store 0 + i)) E ctx rt headerS) :
    ∀ fuel r, Stmt.evalFor fuel E.tbl ctx rt cond .skip (.block []) ≠ .done (.ok r) := by
  have hn := nOf_lt ρ
  have hiw : i < wordSize := by omega
  refine fun fuel => evalFor_never (fun rt => StmtRel (hval ρ i (ρ.store 0 + i)) E ctx rt headerS) ?_ fuel rt hrel
  intro rt h
  have hcond : eraseExpr E.fields headerS cond = some ([], .bin .lt (.arg 1) (.arg 0)) := rfl
  have hev := eval_eq _ E.fields ctx rt headerS h.expr hcond
  refine ⟨1, rt, ?_, by decide, 2, rt.pushScope.popScope, ?_, rt.pushScope.popScope, ?_, ?_⟩
  · have hv : (WExpr.bin .lt (.arg 1) (.arg 0)).eval (hval ρ i (ρ.store 0 + i)) = 1 := by
      simp only [WExpr.eval, BinOp.eval, hval, List.getD_cons_succ, List.getD_cons_zero,
        Nat.mod_eq_of_lt hiw]
      have : i < ρ.args.getD 0 0 % Generic.wordSize := hi
      rw [if_pos this]
      decide
    rw [hev, caught_exprResult]
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, hv]
  · rw [show (2 : Nat) = 1 + 1 from rfl, eval_block_of (evalList_nil 1 E.tbl ctx rt.pushScope)]
    rfl
  · rw [Stmt.eval]; rfl
  · exact h.pushScope.popScope

/-- info: 'Contracts.VerifyCounter.Source.missing_update_never' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms missing_update_never

end Contracts.VerifyCounter.Source

