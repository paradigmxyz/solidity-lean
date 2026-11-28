import Verify.Spec.TreeSucceeds

/-!
# Facts about products of words, for the tree tactics' last step

solc's checked multiplication tests a product by dividing it back (`x == 0 || (x * y) / x == y`),
and a succeeds-if or an ensures bounds a product of arguments (`a * b * c < 2 ** 256`). `omega`
treats a product of two variables as an atom and cannot divide by a variable, so it cannot link
the two. `mul_facts` adds, for every product `a * b` of naturals in the goal and the hypotheses
(neither factor a literal), the equations and bounds `mul_facts_of` states: each factor is at most
the product unless the other is zero, and the product divided by one factor is the other. Each is
a theorem of `Nat`, so nothing is assumed. `mul_close` then turns products of casts into casts of
products, reduces words below `2 ^ 256` and closes with `omega`.
-/

namespace SolidCore.Spec

/-- What `mul_facts` adds for the product `a * b`. -/
theorem mul_facts_of (a b : Nat) :
    (b = 0 ∨ a ≤ a * b) ∧ (a = 0 ∨ b ≤ a * b) ∧ (b = 0 ∨ a * b / b = a) ∧ (a = 0 ∨ a * b / a = b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos b with h | h
    · exact .inl h
    · exact .inr (Nat.le_mul_of_pos_right a h)
  · rcases Nat.eq_zero_or_pos a with h | h
    · exact .inl h
    · exact .inr (Nat.le_mul_of_pos_left b h)
  · rcases Nat.eq_zero_or_pos b with h | h
    · exact .inl h
    · exact .inr (Nat.mul_div_cancel a h)
  · rcases Nat.eq_zero_or_pos a with h | h
    · exact .inl h
    · exact .inr (Nat.mul_div_cancel_left b h)

open Lean Meta Elab Tactic in
/-- For every product `a * b` of naturals in the goal and the hypotheses whose factors are not
literals, and each factor `b` that `omega` shows positive from the hypotheses, add
`a ≤ a * b` and `a * b / b = a` (and the same for `a`); when `omega` bounds both factors by
powers of two whose product is at most `2 ^ 256`, add that bound of the product. Facts only for positive factors, so the
hypotheses gain no disjunction for `omega` to split. -/
elab "mul_facts" : tactic => withMainContext do
  let mut es : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      es := es.push (← instantiateMVars d.type)
  let mut prods : Array (Expr × Expr) := #[]
  for e in es do
    let mut stack := #[e]
    while stack.size > 0 do
      let t := stack.back!
      stack := stack.pop
      if t.isAppOfArity ``HMul.hMul 6 && t.getArg! 0 == mkConst ``Nat then
        let a := t.getArg! 4
        let b := t.getArg! 5
        if !(a.isAppOf ``OfNat.ofNat) && !(b.isAppOf ``OfNat.ofNat) && (a.rawNatLit?).isNone &&
            (b.rawNatLit?).isNone && !a.hasLooseBVars && !b.hasLooseBVars && !prods.contains (a, b) then
          prods := prods.push (a, b)
      match t with
      | .app f x => stack := (stack.push f).push x
      | .mdata _ x => stack := stack.push x
      | _ => pure ()
  let pos (x : Expr) : TacticM (Option Expr) := do
    let ty ← mkAppM ``LT.lt #[mkNatLit 0, x]
    let m ← mkFreshExprMVar ty
    let ok ← try
        let gs ← Tactic.run m.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
        pure gs.isEmpty
      catch _ => pure false
    if ok then return some (← instantiateMVars m) else return none
  -- The least width `k` (a multiple of 8, below 256) with `x < 2 ^ k` by `omega`, and its proof.
  let width (x : Expr) : TacticM (Option (Nat × Expr)) := do
    for i in [1:32] do
      let k := 8 * i
      let ty ← mkAppM ``LT.lt #[x, mkNatLit (2 ^ k)]
      let m ← mkFreshExprMVar ty
      let ok ← try
          let gs ← Tactic.run m.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
          pure gs.isEmpty
        catch _ => pure false
      if ok then return some (k, ← instantiateMVars m)
    return none
  for (a, b) in prods do
    let mut facts : Array Expr := #[]
    if let some hb ← pos b then
      facts := facts ++ #[← mkAppM ``Nat.le_mul_of_pos_right #[a, hb], ← mkAppM ``Nat.mul_div_cancel #[a, hb]]
    if let some ha ← pos a then
      facts := facts ++ #[← mkAppM ``Nat.le_mul_of_pos_left #[b, ha], ← mkAppM ``Nat.mul_div_cancel_left #[b, ha]]
    if let some (ka, ha) ← width a then
      if let some (kb, hb) ← width b then
        if ka + kb ≤ 256 then
          facts := facts.push (← mkAppM ``Nat.mul_lt_mul'' #[ha, hb])
    for pf in facts do
      let g ← getMainGoal
      let (_, g') ← (← g.assert `hmul (← inferType pf) pf).intro1P
      replaceMainGoal [g']

/-- Products of casts as casts of products, words below `2 ^ 256` reduced, `mul_facts`, then
`omega`. -/
macro "mul_close" : tactic => `(tactic| (
  (try clear hreq hinv hst ht)
  (try simp only [← Nat.cast_mul] at *)
  (try simp only [reduceLandLowMask] at *)
  mul_facts
  (try simp (disch := omega) only [Nat.mod_eq_of_lt] at *)
  mul_facts
  omega))

end SolidCore.Spec
