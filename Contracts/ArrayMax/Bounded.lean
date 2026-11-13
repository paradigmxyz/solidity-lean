import Verify.Discharge

/-
A bounded variant of `vc_search` (Verify.Discharge) for obligations whose hypotheses chain a loop
or path condition through many local Booleans, where the unbounded search times out or exhausts
memory (ArrayMax `max`'s preserved quantified invariants) or `vc_norm` exceeds the recursion
limit (Vault's reentrancy-lock obligations):

1. definitions of local symbols are substituted away, and every remaining Boolean constant is
   split into its two cases, so that Boolean formulas fold to literals before `vc_norm`;
2. quantified hypotheses are instantiated once, at the witnesses of existentials and at the
   arguments of matching array reads, and never again;
3. a conditional whose condition has quantifiers (a path condition the context restates) is
   proved from the context by `and_intros`, `assumption` and `omega`, and otherwise split;
4. each case clears its quantified hypotheses and is closed by `omega`.

Every step builds a proof term the kernel checks; a goal it cannot close fails, never passes.
-/
/-
A bounded variant of `vc_search` (Verify.Discharge) for obligations whose hypotheses chain a loop
or path condition through many local Booleans, where the unbounded search times out or exhausts
memory (ArrayMax `max`'s preserved quantified invariants) or `vc_norm` exceeds the recursion
limit (Vault's reentrancy-lock obligations):

1. definitions of local symbols are substituted away, and every remaining Boolean constant is
   split into its two cases, so that Boolean formulas fold to literals before `vc_norm`;
2. quantified hypotheses are instantiated once, at the witnesses of existentials and at the
   arguments of matching array reads, and never again;
3. a conditional whose condition has quantifiers (a path condition the context restates) is
   proved from the context by `and_intros`, `assumption` and `omega`, and otherwise split;
4. each case clears its quantified hypotheses and is closed by `omega`.

Every step builds a proof term the kernel checks; a goal it cannot close fails, never passes.
-/
open Lean Meta Elab Tactic SolarVerify.Discharge

namespace Contracts.Bounded

/-- Like the search's `splitIte`, but proves a quantified condition the context implies
directly in the tactic monad (so a failed attempt is an exception, never a logged error), with
enough depth for a path condition's left-nested conjunction. -/
def splitIteB : TacticM Unit := withMainContext do
  let some c ← findIteCond | throwError "no conditional"
  let hcN ← mkFreshUserName `hc
  let hcI := mkIdent hcN
  if hasQuantifier c then
    let s ← saveState
    try
      let m ← mkFreshExprSyntheticOpaqueMVar c
      let main ← getMainGoal
      setGoals [m.mvarId!]
      evalTactic (← `(tactic| and_intros <;> first | assumption | omega))
      unless (← getGoals).isEmpty do throwError "condition not proved"
      let m ← instantiateMVars m
      if m.hasMVar then throwError "condition not proved"
      let (_, g') ← (← main.assert hcN c m).intro1P
      setGoals [g']
      simpCase (← `(tactic| simp only [↓reduceIte, SolarVerify.Discharge.ite_pos $hcI, SolarVerify.Discharge.qite_pos $hcI]))
      return
    catch _ => s.restore
  evalTactic (← `(tactic| by_cases $hcI : $(← Term.exprToSyntax c)))
  let gs ← getGoals
  let mut out := []
  for (g, pos) in gs.zip [true, false] do
    setGoals [g]
    if pos then
      simpCase (← `(tactic| simp only [↓reduceIte, SolarVerify.Discharge.ite_pos $hcI, SolarVerify.Discharge.qite_pos $hcI]))
    else
      simpCase (← `(tactic| simp only [↓reduceIte, SolarVerify.Discharge.ite_neg $hcI, SolarVerify.Discharge.qite_neg $hcI]))
    out := out ++ (← getGoals)
  setGoals out

/-- Normalizes, splits hypotheses, then splits one conditional or propositional atom per level
(at most `fuel` levels) and closes each case with `omega`, without instantiating again. -/
partial def boundedLeaf (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then throwError "bounded: depth exhausted"
  for g in (← getGoals) do
    setGoals [g]
    evalTactic (← `(tactic| vc_norm))
    if (← getGoals).isEmpty then continue
    splitHyps
    for g in (← getGoals) do
      setGoals [g]
      if (← findIteCond).isSome then
        splitIteB
        boundedLeaf (fuel - 1)
      else if let some p ← findPropAtom then
        splitProp p
        boundedLeaf (fuel - 1)
      else
        clearQuantified
        evalTactic (← `(tactic| omega))
  setGoals []

/-- Substitutes definitions, normalizes, splits hypotheses and instantiates once. -/
def boundedPre : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  iffToEq
  evalTactic (← `(tactic| subst_vars))
  evalTactic (← `(tactic| vc_norm))
  splitHyps
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    let _ ← instantiate (← witnesses) {}
    out := out ++ (← getGoals)
  setGoals out

/-- Cases on every Boolean local variable (an SMT `Bool` constant), so that the Boolean
formulas over it fold to literals before `vc_norm` runs. -/
partial def boolCases : TacticM Unit := withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    if (← instantiateMVars ldecl.type) == mkConst ``Bool then
      let gs ← (← getMainGoal).cases ldecl.fvarId
      let mut out := []
      for sg in gs do
        setGoals [sg.mvarId]
        boolCases
        out := out ++ (← getGoals)
      setGoals out
      return

/-- `boundedPre` with a case split on every Boolean constant before `vc_norm`. -/
def boundedPreB : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  iffToEq
  evalTactic (← `(tactic| subst_vars))
  boolCases
  let gs ← getGoals
  let mut out := []
  for g in gs do
    setGoals [g]
    evalTactic (← `(tactic| simp -failIfUnchanged only [Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false, Bool.not_true, Bool.not_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.false_eq_true, Bool.true_eq_false, false_and, and_false, not_true_eq_false] at *))
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| vc_norm))
    unless (← getGoals).isEmpty do
      splitHyps
    let gs' ← getGoals
    for g' in gs' do
      setGoals [g']
      let _ ← instantiate (← witnesses) {}
      out := out ++ (← getGoals)
  setGoals out

end Contracts.Bounded

open Contracts.Bounded

/-- The bounded search on a goal `vc_valid_prep` left, without Boolean case splits. -/
elab "vc_bounded" : tactic => do boundedPre; boundedLeaf 16

/-- The bounded search on a goal `vc_valid_prep` left, after splitting every Boolean constant. -/
elab "vc_bounded_bool" : tactic => do boundedPreB; boundedLeaf 16

/-- `vc_valid_prep`, then the bounded search with Boolean case splits. -/
macro "vc_bounded_valid" : tactic => `(tactic| (vc_valid_prep <;> vc_bounded_bool))
