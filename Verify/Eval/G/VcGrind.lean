import Verify.Discharge

/-!
# Lane G: vc_grind, grind as the solver behind the exported obligations

The same pipeline as Verify/Discharge/Reconstruct/Tactic.lean's vc_smt, with grind in place of
lean-smt's smt, so that it needs no SMT plugin:

1. vc_valid_prep (Verify/Discharge) reduces Obligation.Valid ob to a shallow goal over Int, Bool
   and functions;
2. vc_grind_norm is vc_smt_norm copied here unchanged (Reconstruct/Tactic.lean imports Smt, so it
   cannot be imported without the plugin): substitute the definitions of local symbols, read every
   if as the classical qite and Booleans as propositions;
3. grind closes the goal. Its proof is a term the kernel checks.

vc_grind_nl adds the nonlinear facts of Verify/Discharge/Nonlinear.lean (vc_nonlinear, when it is
defined there) before grind; vc_grind_only uses grind without its default lemma set.

A grind failure is "unknown", never "sat": grind gives no model.
-/

namespace Verify.Eval.G.VcGrind

/-- Reconstruct/Tactic.lean's ite_eq_qite, copied: an if at any instance is the classical one. -/
theorem ite_eq_qite {α : Type} (c : Prop) [h : Decidable c] (a b : α) :
    @ite α c h a b = SolarVerify.Discharge.qite c a b := by
  unfold SolarVerify.Discharge.qite; congr

end Verify.Eval.G.VcGrind

/-- Reconstruct/Tactic.lean's vc_smt_norm, copied unchanged but for the namespace of ite_eq_qite. -/
macro "vc_grind_norm" : tactic => `(tactic| (
  try subst_vars
  try simp -failIfUnchanged only [Verify.Eval.G.VcGrind.ite_eq_qite] at *
  try simp -failIfUnchanged only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and,
    Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or,
    SolarVerify.Discharge.decide_any_eq_true, SolarVerify.Discharge.qdec_eq_true,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.decide_and, Bool.decide_or,
    decide_not, Bool.eq_false_iff, ne_eq, SolarVerify.Discharge.true_eq_iff,
    SolarVerify.Discharge.false_eq_iff] at *
  try simp -failIfUnchanged only [SolarVerify.Discharge.qite] at *))

macro "vc_grind" : tactic => `(tactic| (vc_valid_prep <;> (intros; vc_grind_norm; grind)))

macro "vc_grind_only" : tactic => `(tactic| (vc_valid_prep <;> (intros; vc_grind_norm; grind only)))
