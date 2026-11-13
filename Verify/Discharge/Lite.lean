import Verify.Discharge.Valid
import Verify.Discharge.Leaf

/-! # A direct leaf for shallow obligations

`vc_lite` closes an obligation whose hypotheses are equations defining its symbols and linear or
Newton-step facts, without the search: after `vc_valid_prep` it substitutes the defining equations,
reads SMT-LIB's Boolean connectives and `div`/`mod` as Lean's (a division by a divisor `omega`
shows nonzero as the plain quotient), adds Nonlinear.lean's facts and
calls `omega`; failing that, it first settles the remaining `if`s from the hypotheses (`simp_all`).
On the Uniswap V2 `Math.sqrt` exports the search instead exceeds `simp`'s step bound on the same
goals. It is tried before `vc_valid`'s search, and fails at once (an `omega` failure, never a
timeout) where it does not apply, leaving the goal to the search.
-/

/-- The leaf of `vc_lite`: `omega` with Nonlinear.lean's facts, then the same after settling the
remaining `if`s, then the same after splitting on the condition of every `if`. -/
macro "vc_lite_leaf" : tactic => `(tactic| first
  | ((try vc_nl_facts) <;> omega)
  | ((try simp_all only [ite_true, ite_false]) <;> (try vc_nl_facts) <;> omega)
  | ((vc_split_ite <;> repeat' vc_split_ite) <;> (try simp only [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_true', Bool.and_eq_true, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, or_true, true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, not_or, Classical.not_not, and_true, true_and] at *) <;> (try vc_nl_facts) <;> omega))

/-- The direct leaf: see the module comment. -/
macro "vc_lite" : tactic => `(tactic| (vc_valid_prep <;> (subst_vars; (try simp only [
    SolarVerify.Discharge.ediv_eq_div,
    SolarVerify.Discharge.emod_eq_mod, Int.reduceEq, decide_false, Bool.not_false, Bool.and_true,
    decide_eq_true_eq, ite_false, ite_true, Bool.not_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    Bool.false_eq_true, or_false, SolarVerify.Discharge.true_eq_iff, Bool.or_eq_true, not_or,
    not_and, Bool.not_eq_true', decide_eq_false_iff_not] at *); (try (vc_fun_defs; subst_vars; simp only [SolarVerify.Discharge.iteFunApply, Bool.and_eq_true, decide_eq_true_eq] at *)); (try simp only [Classical.not_forall, Classical.not_imp, not_and] at *); (try vc_open_exists); (try simp only [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_true', Bool.and_eq_true, Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq, or_true, true_or, or_false, false_or, not_true_eq_false, not_false_eq_true, not_or, Classical.not_not, and_true, true_and] at *); (try simp (disch := omega) only [SolarVerify.Discharge.Nonlinear.ite_div_of_ne] at *); all_goals vc_lite_leaf)))

macro_rules | `(tactic| vc_valid) => `(tactic| vc_lite)
