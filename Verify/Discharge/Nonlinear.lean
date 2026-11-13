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

/-- Comparing a quotient with a bound `k` is comparing `y` with `x * k`. -/
theorem div_ge_iff (y x k : Int) (hx : 1 ≤ x) :
    (k ≤ y / x → x * k ≤ y) ∧ (y / x < k → y < x * k) := by
  have hb := (div_bounds y x).resolve_left (by omega)
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have := Int.mul_le_mul_of_nonneg_left hk (by omega : 0 ≤ x)
    omega
  · have hk' : y / x + 1 ≤ k := by omega
    have := Int.mul_le_mul_of_nonneg_left hk' (by omega : 0 ≤ x)
    rw [Int.mul_add, Int.mul_one] at this
    omega

/-- A square's successor expanded. -/
theorem sq_succ (a : Int) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul]
  omega

/-- The quotient `y / x` against `2`, `x`, `x + 1`, `x + 2` and `x + 3`, read as linear facts over the atom
`x * x` (the comparisons the integer square root's Newton steps need). -/
theorem div_cmp (y x : Int) : ¬ 1 ≤ x ∨
    ((y < x * x ∨ x ≤ y / x) ∧ (x * x ≤ y ∨ y / x < x) ∧
     (y < x * x + x ∨ x + 1 ≤ y / x) ∧ (x * x + x ≤ y ∨ y / x < x + 1) ∧
     (y < x * x + 2 * x ∨ x + 2 ≤ y / x) ∧ (x * x + 2 * x ≤ y ∨ y / x < x + 2) ∧
     (y < x * x + 3 * x ∨ x + 3 ≤ y / x) ∧ (x * x + 3 * x ≤ y ∨ y / x < x + 3) ∧
     (y < 2 * x ∨ 2 ≤ y / x) ∧ (2 * x ≤ y ∨ y / x < 2) ∧
     (x + 1) * (x + 1) = x * x + 2 * x + 1 ∧ 4 * x - 4 ≤ x * x ∧ 2 * x - 1 ≤ x * x) := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have h0 := div_ge_iff y x x hx
  have h1 := div_ge_iff y x (x + 1) hx
  have h2 := div_ge_iff y x (x + 2) hx
  have h3 := div_ge_iff y x (x + 3) hx
  have h4 := div_ge_iff y x 2 hx
  rw [Int.mul_comm x 2] at h4
  rw [Int.mul_add, Int.mul_one] at h1
  rw [Int.mul_add] at h2
  have e : x * 2 = 2 * x := Int.mul_comm x 2
  rw [e] at h2
  rw [Int.mul_add] at h3
  have e3 : x * 3 = 3 * x := Int.mul_comm x 3
  rw [e3] at h3
  have s1 := sq_ge_one x
  have s2 := sq_ge_two x
  have s3 := sq_succ x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s3, s2, s1⟩
  · exact Classical.or_iff_not_imp_left.mpr fun h => Classical.byContradiction fun h' => h (h0.2 (by omega))
  · exact Classical.or_iff_not_imp_right.mpr fun h => h0.1 (by omega)
  · exact Classical.or_iff_not_imp_left.mpr fun h => Classical.byContradiction fun h' => h (h1.2 (by omega))
  · exact Classical.or_iff_not_imp_right.mpr fun h => h1.1 (by omega)
  · exact Classical.or_iff_not_imp_left.mpr fun h => Classical.byContradiction fun h' => h (h2.2 (by omega))
  · exact Classical.or_iff_not_imp_right.mpr fun h => h2.1 (by omega)
  · exact Classical.or_iff_not_imp_left.mpr fun h => Classical.byContradiction fun h' => h (h3.2 (by omega))
  · exact Classical.or_iff_not_imp_right.mpr fun h => h3.1 (by omega)
  · exact Classical.or_iff_not_imp_left.mpr fun h => Classical.byContradiction fun h' => h (h4.2 (by omega))
  · exact Classical.or_iff_not_imp_right.mpr fun h => h4.1 (by omega)

/-- A Newton step from `x ≥ 1` on `y ≥ 4` stays at least 2 (from `newton_lt`). -/
theorem newton_ge_two (y x : Int) : ¬ 1 ≤ x ∨ ¬ 4 ≤ y ∨ 2 ≤ (y / x + x) / 2 := by
  refine Classical.or_iff_not_imp_left.mpr fun hx => Classical.or_iff_not_imp_left.mpr fun hy => ?_
  have hx : 1 ≤ x := Classical.not_not.mp hx
  have hy : 4 ≤ y := Classical.not_not.mp hy
  have h := ((newton_lt y x).resolve_left (by omega)).resolve_left (by omega)
  have hq0 : 0 ≤ y / x := Int.ediv_nonneg (by omega) (by omega)
  have hn0 : 0 ≤ (y / x + x) / 2 := by omega
  generalize (y / x + x) / 2 = n at *
  refine Classical.byContradiction fun hc => ?_
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl <;> simp at h <;> omega

/-- SMT-LIB's total division, `if x = 0 then divZero y else y / x`, is `y / x` off zero. -/
theorem ite_div (x a y : Int) (inst : Decidable (x = 0)) :
    x = 0 ∨ @ite Int (x = 0) inst a (y / x) = y / x := by
  refine Classical.or_iff_not_imp_left.mpr fun h => ?_
  exact @if_neg (x = 0) inst h Int a (y / x)

/-- `ite_div` as a rewrite, for `simp` with a discharger that proves `x ≠ 0`. -/
theorem ite_div_of_ne {x a y : Int} [Decidable (x = 0)] (h : ¬ x = 0) :
    (if x = 0 then a else y / x) = y / x := if_neg h

open Lean Meta Elab Tactic

/-- Whether `e` is a numeral. -/
def isNumeral (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 || e.nat?.isSome || e.int?.isSome

/-- Whether `e` is the numeral 2. -/
def isTwo (e : Expr) : Bool :=
  e.nat? == some 2 || e.int? == some 2 ||
    (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 2)

/-- Whether `e` is the numeral 1. -/
def isOne (e : Expr) : Bool :=
  e.nat? == some 1 || e.int? == some 1 ||
    (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 1)

/-- The facts the terms of `e` call for: a lemma and its arguments. -/
partial def scan (e : Expr) (acc : Array (Name × Array Expr)) : MetaM (Array (Name × Array Expr)) := do
  let mut acc := acc
  if !e.hasLooseBVars then
    -- SMT-LIB's total division: `if x = 0 then a else y / x`
    if e.isAppOfArity ``ite 5 then
      let c := e.getArg! 1
      let b := e.getArg! 4
      if c.isAppOfArity ``Eq 3 && b.isAppOfArity ``HDiv.hDiv 6 && b.getArg! 5 == c.getArg! 1 then
        acc := acc.push (``ite_div, #[c.getArg! 1, e.getArg! 3, b.getArg! 4, e.getArg! 2])
    if e.isAppOfArity ``HDiv.hDiv 6 && (e.getArg! 0).isConstOf ``Int then
      let a := e.getArg! 4
      let b := e.getArg! 5
      if !isNumeral b then
        acc := acc.push (``div_bounds, #[a, b])
        acc := acc.push (``div_facts, #[a, b])
        acc := acc.push (``div_cmp, #[a, b])
      else if a.isAppOfArity ``HAdd.hAdd 6 && isTwo b then
        let l := a.getArg! 4
        let r := a.getArg! 5
        if l.isAppOfArity ``HDiv.hDiv 6 && l.getArg! 5 == r then
          acc := acc.push (``newton_lt, #[l.getArg! 4, r])
          acc := acc.push (``newton_le, #[l.getArg! 4, r])
          acc := acc.push (``newton_ge_two, #[l.getArg! 4, r])
    else if e.isAppOfArity ``HMul.hMul 6 && (e.getArg! 0).isConstOf ``Int && e.getArg! 4 == e.getArg! 5 then
      acc := acc.push (``sq_ge_one, #[e.getArg! 4])
      acc := acc.push (``sq_ge_two, #[e.getArg! 4])
      let p := e.getArg! 4
      if p.isAppOfArity ``HAdd.hAdd 6 && isOne (p.getArg! 5) then
        acc := acc.push (``sq_succ, #[p.getArg! 4])
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

/-- The condition of an `if` over a non-proposition in `e` (not a division's zero test), if any. -/
partial def findIteCond (e : Expr) : MetaM (Option Expr) := do
  if !e.hasLooseBVars && e.isAppOfArity ``ite 5 then
    let c := e.getArg! 1
    let isDivZero := c.isAppOfArity ``Eq 3 && (e.getArg! 4).isAppOfArity ``HDiv.hDiv 6
    if !isDivZero && !(← isProp (e.getArg! 0)) && !c.hasLooseBVars then return some c
  match e with
  | .app f a => match ← findIteCond f with | some c => pure (some c) | none => findIteCond a
  | .lam _ t b _ | .forallE _ t b _ =>
    match ← findIteCond t with | some c => pure (some c) | none => findIteCond b
  | .mdata _ b => findIteCond b
  | _ => pure none

/-- Splits on the condition `c` of an `if` in the context: the goal becomes `c ∨ ¬ c → G`. -/
def splitIte : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let mut cond ← findIteCond (← instantiateMVars (← g.getType))
  for d in ← getLCtx do
    if cond.isSome then break
    if d.isImplementationDetail then continue
    if ← isProp d.type then cond ← findIteCond (← instantiateMVars d.type)
  let some c := cond | throwError "vc_split_ite: no if"
  let pf ← mkAppM ``Classical.em #[c]
  replaceMainGoal [← g.assert `vc_ite_h (← inferType pf) pf]

elab "vc_ite_em" : tactic => splitIte

/-- Case split on the condition of an `if` in the context, which `simp` then removes. -/
macro "vc_split_ite" : tactic => `(tactic| (vc_ite_em; rintro (hc | hc) <;>
  (first | simp only [ite_cond_eq_true _ _ (eq_true hc)] at * | simp only [ite_cond_eq_false _ _ (eq_false hc)] at *) <;>
  try subst_vars))

/-- A pointwise definition of a function symbol as an equation `subst` can use. -/
theorem fun_eq_of_forall {α β : Sort _} {f : α → β} {g : α → β} (h : ∀ k, f k = g k) :
    f = fun k => g k := funext h

/-- A pointwise definition of a two-argument function symbol (a nested array). -/
theorem fun_eq_of_forall2 {α β γ : Sort _} {f : α → β → γ} {g : α → β → γ} (h : ∀ k j, f k j = g k j) :
    f = fun k j => g k j := funext fun k => funext (h k)

/-- Turns each hypothesis `h : ∀ k, f k = e[k]` with `f` a local variable into `f = fun k => e[k]`. -/
def funDefs : TacticM Unit := withMainContext do
  let mut changed := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let .forallE n dom body _ := ty | continue
    -- two levels: `∀ k j, f k j = e[k, j]`
    if let .forallE n2 dom2 body2 _ := body then
      if body2.isAppOfArity ``Eq 3 && !dom2.hasLooseBVars then
        let lhs := body2.getArg! 1
        if lhs.isApp && lhs.appArg! == .bvar 0 && lhs.appFn!.isApp && lhs.appFn!.appArg! == .bvar 1 &&
            lhs.appFn!.appFn!.isFVar && !(body2.getArg! 2).containsFVar lhs.appFn!.appFn!.fvarId! then
          let rhsLam := Expr.lam n dom (Expr.lam n2 dom2 (body2.getArg! 2) .default) .default
          let g ← getMainGoal
          let pf ← mkAppOptM ``fun_eq_of_forall2 #[none, none, none, some lhs.appFn!.appFn!, some rhsLam,
            some (.fvar d.fvarId)]
          let g ← g.assert `vc_fdef (← inferType pf) pf
          let (_, g) ← g.intro1P
          let g ← g.tryClear d.fvarId
          replaceMainGoal [g]
          changed := true
      continue
    unless body.isAppOfArity ``Eq 3 do continue
    let lhs := body.getArg! 1
    unless lhs.isApp && lhs.appArg! == .bvar 0 && lhs.appFn!.isFVar do continue
    if (body.getArg! 2).containsFVar lhs.appFn!.fvarId! then continue
    let rhsLam := Expr.lam n dom (body.getArg! 2) .default
    let g ← getMainGoal
    let pf ← mkAppOptM ``fun_eq_of_forall #[none, none, some lhs.appFn!, some rhsLam, some (.fvar d.fvarId)]
    let g ← g.assert `vc_fdef (← inferType pf) pf
    let (_, g) ← g.intro1P
    let g ← g.tryClear d.fvarId
    replaceMainGoal [g]
    changed := true
  unless changed do throwError "vc_fun_defs: none"

elab "vc_fun_defs" : tactic => funDefs

/-- Destructures every hypothesis that is an `∃` or an `∧`. -/
partial def openExists : TacticM Unit := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
      let gs ← (← getMainGoal).cases d.fvarId
      replaceMainGoal (gs.map (·.mvarId)).toList
      openExists
      return

elab "vc_open_exists" : tactic => openExists

end SolarVerify.Discharge.Nonlinear
