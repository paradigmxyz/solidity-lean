import Lean
import Mathlib.Tactic.SplitIfs

/-!
# The baseline closing cascade, copied from Verify/Tactic.lean (lane H)

`sc_bounds`, `sc_arith` and `sc_close` exactly as in `Verify/Tactic.lean` (that module imports the
SolidCore refinement; these do not need it), so the mutation tests run the baseline's closer on the
goals every engine leaves.
-/

namespace Verify.Eval.H.Close

open Lean Elab Tactic in
partial def bitTerms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let acc :=
    if (e.isAppOfArity ``HXor.hXor 6 || e.isAppOfArity ``HOr.hOr 6 || e.isAppOfArity ``HAnd.hAnd 6) &&
        !e.hasLooseBVars && e.appFn!.appFn!.appFn!.appFn!.appFn!.appArg! == mkConst ``Nat &&
        !acc.contains e then acc.push e
    else acc
  match e with
  | .app f a => bitTerms a (bitTerms f acc)
  | .lam _ t b _ | .forallE _ t b _ => bitTerms b (bitTerms t acc)
  | .letE _ t v b _ => bitTerms b (bitTerms v (bitTerms t acc))
  | .mdata _ b | .proj _ _ b => bitTerms b acc
  | _ => acc

open Lean Elab Tactic in
elab "sc_bounds" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  for e in bitTerms ty do
    let stx ← (← getMainGoal).withContext do Term.exprToSyntax e
    for n in (List.range 32).map (8 * · + 8) do
      let ok ← try
          evalTactic (← `(tactic| have : $stx < 2 ^ $(quote n) := by
            first
              | exact Nat.xor_lt_two_pow (by omega) (by omega)
              | exact Nat.or_lt_two_pow (by omega) (by omega)
              | exact Nat.lt_of_le_of_lt Nat.and_le_left (by omega)))
          pure true
        catch _ => pure false
      if ok then break

macro "sc_arith" : tactic => `(tactic| first
  | done
  | trivial
  | rfl
  | (simp_all; done)
  | omega
  | (sc_bounds; omega)
  | (congr 1 <;> (sc_bounds; omega))
  | (simp only [Nat.reducePow] at *; sc_bounds; omega)
  | bv_omega
  | decide
  | (simp_all <;> (sc_bounds; omega)))

macro "sc_close" : tactic => `(tactic| (
  try split_ifs
  all_goals try dsimp only
  all_goals repeat' (first | apply And.intro | intro)
  all_goals try split_ifs
  all_goals repeat' (first | apply And.intro | intro)
  all_goals sc_arith))

end Verify.Eval.H.Close
