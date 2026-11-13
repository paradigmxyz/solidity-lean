import SolidCore.Verify.Run
import SolidCore.Verify.Finite

/-!
# One tactic for the verification conditions

`sc_vcgen [defs]` proves the verification conditions of a model on `Abi.fullScope`, the goal
`∀ call, scope call → pre call → vc model (argWords n) post call`, where `defs` are the
definitions to unfold: the scope, the function list, the model, the postcondition and
whatever they mention. It

1. reduces the scope to `Abi.fullScope` (`vcs_of_fullScope`), one goal per function and
   list of argument words, with the call's argument words and initial storage known;
2. introduces the argument words (up to four) and their bounds;
3. computes Loom's weakest precondition of the model with `wp_bind`, `wp_pure` and the
   rules of `Verify.Basic` and `Verify.Finite` (`wp_sload`, `wp_sstore`, `wp_revert`,
   `wp_ite`, `wp_ofPure`);
4. closes what is left, a goal on words, with a fixed cascade (`sc_close`): split the
   `if`s, the conjunctions and the quantifiers, then `simp_all`, `omega`, `bv_omega` and
   `decide`. It never calls `bv_decide` or `native_decide`, so its proofs rest on the
   kernel alone.

A scope that is a subset of `Abi.fullScope`, such as the finite `· ∈ Abi.calls fns [s]`,
goes through `vcs_mono` first.
-/

namespace SolidCore.Verify

open Lean Elab Tactic

/-- The bitwise `&&&`, `|||` and `^^^` terms on `Nat` in `e` that mention no bound variable. -/
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

/-- For each bitwise term on `Nat` in the goal, adds the bound `t < 2 ^ n` at the least byte
width `n` its operands fit, as `omega` shows, so that `omega`, which treats the term as an
atom, knows it. -/
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

/-- The closing cascade on a goal on words. -/
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

/-- Splits a goal on words into its cases and closes each with `sc_arith`. -/
macro "sc_close" : tactic => `(tactic| (
  try split_ifs
  all_goals try dsimp only
  all_goals repeat' (first | apply And.intro | intro)
  all_goals try split_ifs
  all_goals repeat' (first | apply And.intro | intro)
  all_goals sc_arith))

/-- The verification conditions of a model on `Abi.fullScope` (see the module docs). -/
syntax "sc_vcgen" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| sc_vcgen) => `(tactic| sc_vcgen [])
  | `(tactic| sc_vcgen [$ts,*]) => do
    let ts : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      ts.getElems.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| set_option linter.unusedSimpArgs false in (
      try simp only [$ts,*]
      refine vcs_of_fullScope (by simp [$ts,*]) ?_
      intro fn hfn call args hcall hw hlen hargs hinit hpre
      simp only [$ts,*, List.mem_cons, List.not_mem_nil, or_false] at hfn
      try casesm* _ ∨ _
      all_goals subst fn
      all_goals rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _⟩⟩⟩⟩
      all_goals try (simp at hlen; done)
      all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, imp_false, not_false_eq_true, implies_true, and_true, IsEmpty.forall_iff] at hargs
      all_goals simp only [$ts,*, hw, wp_bind, wp_pure, wp_sload, wp_sstore, wp_revert, wp_ite,
        wp_ofPure, List.getD_cons_zero, List.getD_cons_succ, ite_apply, dite_apply, SolidCore.Refinement.slotValue,
        List.foldl_cons, List.foldl_nil]
      all_goals sc_close))

end SolidCore.Verify
