import SolidCore.Refinement.Generic.CanonCmp

/-!
# Audit: comparisons in one spelling

Each proved declaration has the exact statement of its challenge (`example`), and its axioms are
at most `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`).
-/

namespace SolidCore.Refinement.Generic.Audit

open SolidCore.Refinement.Generic

example : ∀ (ρ : Val) (op : BinOp) (a b : WExpr), (cmpBin op a b).eval ρ = (WExpr.bin op a b).eval ρ := @cmpBin_eval

example : ∀ (ρ : Val) (e : WExpr), e.cmp.eval ρ = e.eval ρ := @WExpr.eval_cmp

example : ∀ (ρ : Val) (T : Tree), T.cmp.eval ρ = T.eval ρ := @Tree.eval_cmp

example : ∀ (ρ : Val) (U : Tree), U.cmpCanon.eval ρ = U.eval ρ := @Tree.eval_cmpCanon

example : ∀ (ρ : Val) (T : Tree), T.canonCmp.eval ρ = T.eval ρ := @Tree.eval_canonCmp

example : ∀ {t1 t2 : Tree}, Tree.agree t1 t2 = true → ∀ ρ : Val, t1.eval ρ = t2.eval ρ := @Tree.eval_of_agree

example : ∀ {t1 t2 : Tree}, t1.canon.beq t2.canon = true → Tree.agree t1 t2 = true := @Tree.agree_of_beq

end SolidCore.Refinement.Generic.Audit

#print axioms SolidCore.Refinement.Generic.cmpBin_eval
#print axioms SolidCore.Refinement.Generic.WExpr.eval_cmp
#print axioms SolidCore.Refinement.Generic.Tree.eval_cmp
#print axioms SolidCore.Refinement.Generic.Tree.eval_cmpCanon
#print axioms SolidCore.Refinement.Generic.Tree.eval_canonCmp
#print axioms SolidCore.Refinement.Generic.Tree.eval_of_agree
#print axioms SolidCore.Refinement.Generic.Tree.agree_of_beq
