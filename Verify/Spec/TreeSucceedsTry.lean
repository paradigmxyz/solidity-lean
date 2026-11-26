import Verify.Spec.TreeSucceeds

/-!
# `tree_succeeds_try`: `tree_succeeds` with every step allowed to change nothing

`tree_succeeds` fails with "simp made no progress" when one of its simplification steps has
nothing to rewrite, as for a succeeds-if condition over the call's environment alone
(`msg.value == 0`). `tree_succeeds_try [defs]` runs the same steps, each under `try`, with the
local hypotheses added to the definitions it unfolds, and the same closing tactics, so it proves
the same statement, `TreeSucceeds b fs ctx n T` (or `TreeSucceedsAt`, after its caller's
`intro`), wherever `tree_succeeds` does and also where a step is idle.
-/

namespace SolidCore.Spec

open SolidCore.Refinement SolidCore.Refinement.Generic

macro "tree_succeeds_try" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro args s iargs pre hl hargs hs hdec hst ht hreq hinv hsi
  try simp only [Nat.reducePow] at hs
  rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    (try simp only [List.length_cons, List.length_nil] at hl) <;> (try omega) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Nat.reducePow] at hargs) <;>
    (try simp only [$ds,*, *, List.head, List.getElem_cons_zero, List.getElem_cons_succ, decodeWords,
      Ty.ofWord, bind, pure, Option.bind, Nat.reducePow] at hdec) <;>
    (try split_ifs at hdec) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hdec) <;>
    (try subst hdec)
  all_goals try simp only [$ds,*, *, Tree.eval, WExpr.eval, BinOp.eval, UnOp.eval, Generic.wordSize,
    Res.obs, Writes.store, List.getD_cons_zero, List.getD_cons_succ, Nat.reducePow]
  all_goals try simp (disch := simp only [hargs, hs, Nat.reduceLT]) only [Nat.mod_eq_of_lt, ite_mod_nat,
    Nat.reduceMod, Nat.zero_mod, ite10_eq_zero_iff, Decidable.not_not]
  all_goals try simp only [Bundle.satAll, Bundle.sat, $ds,*, *, List.getElem_cons_succ,
    List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, eval,
    evalList, slotOf, mkEnv, Env.cur, Env.bind, BinOp.apply, Ty.ofBits, toWord, List.getD_cons_zero,
    List.getD_cons_succ, List.lookup, ofProp_ne_zero, ite_true, ite_false, Bool.false_eq_true,
    Nat.zero_mod, hst, beq_self_eq_true, Ty.InRange, Option.getD_some, forall_int_range, Nat.cast_ofNat,
    Int.reducePow] at hsi
  all_goals try simp only [wordMod, Nat.reducePow] at hsi
  all_goals try simp (disch := first | exact hs _ | omega) only [Nat.cast_ofNat,
    Int.reduceMod, Int.reduceToNat, Nat.mod_eq_of_lt, toNat_natCast_emod, toNat_ofNat_emod,
    toNat_zero_emod, toNat_one_emod, wordMod, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.div_one,
    Nat.reduceDiv, Int.reducePow] at hsi
  all_goals ((try split_ifs) <;> (try rfl) <;> first | omega | (simp_all; done) | (simp_all; omega))))

end SolidCore.Spec
