import Verify.Discharge.Valid
import Verify.Discharge.Leaf

/-! # A direct leaf for shallow obligations

`vc_lite` closes an obligation whose hypotheses are equations defining its symbols and linear or
Newton-step facts, without the search: after `vc_valid_prep` it substitutes the defining equations,
reads SMT-LIB's Boolean connectives and `div`/`mod` as Lean's, adds Nonlinear.lean's facts and
calls `omega`; failing that, it first settles the remaining `if`s from the hypotheses (`simp_all`).
On the Uniswap V2 `Math.sqrt` exports the search instead exceeds `simp`'s step bound on the same
goals. It is tried before `vc_valid`'s search, and fails at once (an `omega` failure, never a
timeout) where it does not apply, leaving the goal to the search.
-/

/-- The direct leaf: see the module comment. -/
macro "vc_lite" : tactic => `(tactic| (vc_valid_prep <;> (subst_vars; simp only [SolarVerify.Discharge.ediv_eq_div,
    SolarVerify.Discharge.emod_eq_mod, Int.reduceEq, decide_false, Bool.not_false, Bool.and_true,
    decide_eq_true_eq, ite_false, ite_true, Bool.not_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    Bool.false_eq_true, or_false, SolarVerify.Discharge.true_eq_iff, Bool.or_eq_true, not_or,
    not_and, Bool.not_eq_true', decide_eq_false_iff_not] at *; (first | ((try vc_nl_facts) <;> omega) | ((try simp_all only [ite_true, ite_false]) <;> (try vc_nl_facts) <;> omega)))))

macro_rules | `(tactic| vc_valid) => `(tactic| vc_lite)
