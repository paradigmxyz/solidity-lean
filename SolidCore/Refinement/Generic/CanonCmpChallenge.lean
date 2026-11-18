import SolidCore.Refinement.Generic.CanonCmp

/-!
# Challenge: comparisons in one spelling

The exact statements, each with `sorry`: a statement file only. Nothing imports it and no proof
uses it; `CanonCmpAudit` checks each proved declaration against the statement here
(`example : <statement> := <declaration>`).
-/

namespace SolidCore.Refinement.Generic.Challenge

open SolidCore.Refinement.Generic

theorem cmpBin_eval : ∀ (ρ : Val) (op : BinOp) (a b : WExpr), (cmpBin op a b).eval ρ = (WExpr.bin op a b).eval ρ := sorry

theorem WExpr_eval_cmp : ∀ (ρ : Val) (e : WExpr), e.cmp.eval ρ = e.eval ρ := sorry

theorem Tree_eval_cmp : ∀ (ρ : Val) (T : Tree), T.cmp.eval ρ = T.eval ρ := sorry

theorem Tree_eval_cmpCanon : ∀ (ρ : Val) (U : Tree), U.cmpCanon.eval ρ = U.eval ρ := sorry

theorem Tree_eval_canonCmp : ∀ (ρ : Val) (T : Tree), T.canonCmp.eval ρ = T.eval ρ := sorry

theorem Tree_eval_of_agree : ∀ {t1 t2 : Tree}, Tree.agree t1 t2 = true → ∀ ρ : Val, t1.eval ρ = t2.eval ρ := sorry

theorem Tree_agree_of_beq : ∀ {t1 t2 : Tree}, t1.canon.beq t2.canon = true → Tree.agree t1 t2 = true := sorry

end SolidCore.Refinement.Generic.Challenge
