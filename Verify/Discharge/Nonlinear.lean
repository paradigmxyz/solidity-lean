import Lean

/-!
# Nonlinear facts for the search's leaves

`omega` reads a product of two variables, or a division by a variable, as an atom it knows
nothing about. `vc_nl_facts` adds, for the terms of the context, facts proved once here that
relate those atoms to the rest, so that `omega` can finish:

* for every square `P * P`: `2 * P - 1 ≤ P * P` and `4 * P - 4 ≤ P * P` (from
  `0 ≤ (P - k) * (P - k)`);
* for every `y / x` with `x` not a literal: `x * (y / x) ≤ y < x * (y / x) + x` when `1 ≤ x`, and
  when also `0 ≤ y`: `0 ≤ y / x ≤ y`, `1 ≤ y / x` when `x ≤ y`, `y / x = 0` when `y < x`;
* for every Newton step `(y / x + x) / 2` of the integer square root: the step's successor
  squared exceeds `y` (the arithmetic-geometric mean inequality), and the step is below `x`
  unless `x * x ≤ y`.

Every fact is a theorem below, so a leaf closed this way is closed by `omega` from true premises;
`discharge.sh` checks each proof's axioms in any case.
-/

namespace SolarVerify.Discharge.Nonlinear

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (by omega) (by omega)

theorem sq_ge_one (P : Int) : 2 * P - 1 ≤ P * P := by
  have h := sq_nonneg (P - 1)
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_one, Int.one_mul] at h
  omega

theorem sq_ge_two (P : Int) : 4 * P - 4 ≤ P * P := by
  have h := sq_nonneg (P - 2)
  simp only [Int.sub_mul, Int.mul_sub] at h
  have : (2 : Int) * P = P * 2 := Int.mul_comm 2 P
  omega

theorem div_bounds (y x : Int) : ¬ 1 ≤ x ∨ (x * (y / x) ≤ y ∧ y < x * (y / x) + x) := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have h1 := Int.emod_def y x
  have h2 := Int.emod_nonneg y (by omega : x ≠ 0)
  have h3 := Int.emod_lt_of_pos y (by omega : 0 < x)
  omega


/-- The quotient of a nonnegative `y` by a positive `x`: nonnegative, at most `y`, at least 1 when
`x ≤ y`, and 0 when `y < x`. -/
theorem div_facts (y x : Int) : ¬ 1 ≤ x ∨ ¬ 0 ≤ y ∨
    (0 ≤ y / x ∧ y / x ≤ y ∧ (¬ x ≤ y ∨ 1 ≤ y / x) ∧ (¬ y < x ∨ y / x = 0)) := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => Classical.or_iff_not_imp_left.mpr fun hy => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have hy : 0 ≤ y := Classical.not_not.mp hy
  have hb := (div_bounds y x).resolve_left (by omega)
  have hq0 : 0 ≤ y / x := Int.ediv_nonneg hy (by omega)
  have hxq : 1 * (y / x) ≤ x * (y / x) := Int.mul_le_mul_of_nonneg_right hx hq0
  rw [Int.one_mul] at hxq
  refine ⟨hq0, by omega, ?_, ?_⟩
  · refine Classical.or_iff_not_imp_left.mpr fun hxy => ?_
    have hxy : x ≤ y := Classical.not_not.mp hxy
    refine Classical.byContradiction fun hc => ?_
    have h0 : y / x = 0 := by omega
    rw [h0, Int.mul_zero] at hb
    omega
  · refine Classical.or_iff_not_imp_left.mpr fun hlt => ?_
    have hlt : y < x := Classical.not_not.mp hlt
    refine Classical.byContradiction fun hc => ?_
    have h1 : 1 ≤ y / x := by omega
    have := Int.mul_le_mul_of_nonneg_left h1 (by omega : 0 ≤ x)
    rw [Int.mul_one] at this
    omega

theorem newton_lt (y x : Int) :
    ¬ 1 ≤ x ∨ ¬ 0 ≤ y ∨ y < ((y / x + x) / 2 + 1) * ((y / x + x) / 2 + 1) := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => Classical.or_iff_not_imp_left.mpr fun hy => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have hy : 0 ≤ y := Classical.not_not.mp hy
  have h2 := ((div_bounds y x).resolve_left (by omega)).2
  have hq0 : 0 ≤ y / x := Int.ediv_nonneg hy (by omega)
  generalize hq : y / x = q at *
  generalize hm : (q + x) / 2 + 1 = m
  have hm2 : q + 1 + x ≤ 2 * m := by omega
  have hsq : (q + 1 + x) * (q + 1 + x) ≤ (2 * m) * (2 * m) :=
    Int.mul_le_mul hm2 hm2 (by omega) (by omega)
  have e : (2 * m) * (2 * m) = 2 * (2 * (m * m)) := by
    rw [Int.mul_assoc, Int.mul_left_comm m 2 m]
  rw [e] at hsq
  have hamgm := sq_nonneg (q + 1 - x)
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_one, Int.one_mul] at hsq hamgm
  have c1 : q * x = x * q := Int.mul_comm q x
  omega

theorem newton_le (y x : Int) : ¬ 1 ≤ x ∨ ¬ x ≤ (y / x + x) / 2 ∨ x * x ≤ y := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => Classical.or_iff_not_imp_left.mpr fun h => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have h : x ≤ (y / x + x) / 2 := Classical.not_not.mp h
  have h1 := ((div_bounds y x).resolve_left (by omega)).1
  have hq : x ≤ y / x := by omega
  have := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ x)
  omega

open Lean Meta Elab Tactic

/-- Whether `e` is a numeral. -/
def isNumeral (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 || e.nat?.isSome || e.int?.isSome

/-- Whether `e` is the numeral 2. -/
def isTwo (e : Expr) : Bool :=
  e.nat? == some 2 || e.int? == some 2 ||
    (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 2)

/-- The facts the terms of `e` call for: a lemma and its arguments. -/
partial def scan (e : Expr) (acc : Array (Name × Array Expr)) : MetaM (Array (Name × Array Expr)) := do
  let mut acc := acc
  if !e.hasLooseBVars then
    if e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 0).isConstOf ``Int then
      let a := e.getArg! 4
      let b := e.getArg! 5
      if !isNumeral b then
        acc := acc.push (``div_bounds, #[a, b])
        acc := acc.push (``div_facts, #[a, b])
      else if a.isAppOfArity ``HAdd.hAdd 6 && isTwo b then
        let l := a.getArg! 4
        let r := a.getArg! 5
        if l.isAppOfArity ``HDiv.hDiv 6 && l.getArg! 5 == r then
          acc := acc.push (``newton_lt, #[l.getArg! 4, r])
          acc := acc.push (``newton_le, #[l.getArg! 4, r])
    else if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf ``Int && e.getArg! 4 == e.getArg! 5 then
      acc := acc.push (``sq_ge_one, #[e.getArg! 4])
      acc := acc.push (``sq_ge_two, #[e.getArg! 4])
  match e with
  | .app f a => scan a (← scan f acc)
  | .lam _ t b _ | .forallE _ t b _ => scan b (← scan t acc)
  | .mdata _ b => scan b acc
  | _ => pure acc

/-- Adds the nonlinear facts the context's terms call for; fails when there are none. -/
def addFacts : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let mut acc := #[]
  acc ← scan (← instantiateMVars (← g.getType)) acc
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then acc ← scan (← instantiateMVars d.type) acc
  let mut seen : Array Expr := #[]
  let mut g := g
  for (n, args) in acc do
    let pf ← mkAppM n args
    if seen.contains pf then continue
    seen := seen.push pf
    let (_, g') ← (← g.assert `nl (← inferType pf) pf).intro1P
    g := g'
  if seen.isEmpty then throwError "vc_nl_facts: no nonlinear term"
  replaceMainGoal [g]

/-- Adds the facts above for the terms of the context (see the module comment). -/
elab "vc_nl_facts" : tactic => addFacts

end SolarVerify.Discharge.Nonlinear
