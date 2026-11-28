import Verify.Spec.MulFacts

/-!
# Packed storage fields read back after a write

SolidCore writes a packed field by clearing its bits and or-ing in the new value: a field in the low
`k` bits of a slot becomes `(s &&& m) ||| v`, with `m = 2 ^ 256 - 2 ^ k` keeping the higher fields and
`v < 2 ^ k` the new value. A later read of a higher field divides that word by `2 ^ k` or more,
which `omega` cannot see through `|||`. `lor_highMask` states the word as `s % 2 ^ 256 / 2 ^ k * 2 ^ k + v`,
which `omega` reads; `reduceLorHighMask` applies it wherever the mask is such a literal, as an
`if v < 2 ^ k` whose condition the caller discharges (`packed_close`). Each rewrite is a theorem of `Nat`.
-/

namespace SolidCore.Spec

/-- The bits of `2 ^ n - 2 ^ k`: those from `k` below `n`. -/
theorem testBit_two_pow_sub_two_pow {n k : Nat} (hk : k ≤ n) (i : Nat) :
    (2 ^ n - 2 ^ k).testBit i = (decide (k ≤ i) && decide (i < n)) := by
  have h : 2 ^ n - 2 ^ k = 2 ^ k * (2 ^ (n - k) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  rw [h, Nat.mul_comm, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : k ≤ i <;> simp [hi]
  omega

/-- **A word with its low `k` bits replaced by `v < 2 ^ k`**, as an arithmetic term. -/
theorem lor_highMask (x v k : Nat) (hk : k ≤ 256) (hv : v < 2 ^ k) :
    (x &&& (2 ^ 256 - 2 ^ k)) ||| v = x % 2 ^ 256 / 2 ^ k * 2 ^ k + v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hv, Nat.testBit_or, Nat.testBit_and,
    testBit_two_pow_sub_two_pow hk]
  by_cases hi : i < k
  · have : ¬ k ≤ i := by omega
    simp [hi, this]
  · have hki : k ≤ i := by omega
    have hvi : v.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hki))
    rw [if_neg hi, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.sub_add_cancel hki, hvi]
    simp [hki, Bool.and_comm]

/-- `lor_highMask` under its condition: what `reduceLorHighMask` rewrites to. -/
theorem lor_highMask_ite (x v k : Nat) (hk : k ≤ 256) :
    (x &&& (2 ^ 256 - 2 ^ k)) ||| v =
      if v < 2 ^ k then x % 2 ^ 256 / 2 ^ k * 2 ^ k + v else (x &&& (2 ^ 256 - 2 ^ k)) ||| v := by
  split
  · exact lor_highMask x v k hk (by assumption)
  · rfl

/-- The same with the masked word reduced modulo `2 ^ 256` first, as the erased trees write it. -/
theorem lor_highMask_mod_ite (x v k : Nat) (hk : k ≤ 256) :
    (x &&& (2 ^ 256 - 2 ^ k)) % 2 ^ 256 ||| v =
      if v < 2 ^ k then x % 2 ^ 256 / 2 ^ k * 2 ^ k + v
      else (x &&& (2 ^ 256 - 2 ^ k)) % 2 ^ 256 ||| v := by
  split
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by omega))]
    exact lor_highMask x v k hk (by assumption)
  · rfl

/-- A field read back from above the low field: dividing the rewritten word by the low field's
width drops the low value. -/
theorem add_mul_div_of_lt {a b k : Nat} (hb : b < k) : (a * k + b) / k = a := by
  have hk : 0 < k := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hb, Nat.zero_add]

open Lean Meta Simp in
/-- `(x &&& m) ||| v` and `(x &&& m) % 2 ^ 256 ||| v` for a literal `m = 2 ^ 256 - 2 ^ k` (`0 < k < 256`): the
arithmetic word of `lor_highMask_ite`. -/
simproc_decl reduceLorHighMask ((_ : Nat) ||| _) := fun e => do
  let_expr HOr.hOr _ _ _ _ a v ← e | return .continue
  let (x, m, modded) ← match_expr a with
    | HAnd.hAnd _ _ _ _ x m => pure (x, m, false)
    | HMod.hMod _ _ _ _ b n =>
      let some nv ← Nat.fromExpr? n | return .continue
      unless nv = 2 ^ 256 do return .continue
      let_expr HAnd.hAnd _ _ _ _ x m ← b | return .continue
      pure (x, m, true)
    | _ => return .continue
  let some mv ← Nat.fromExpr? m | return .continue
  unless mv < 2 ^ 256 do return .continue
  let low := 2 ^ 256 - mv
  let k := low.log2
  unless 0 < k ∧ k < 256 ∧ low = 2 ^ k do return .continue
  let hk ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit k, mkNatLit 256])
  let pf ← mkAppM (if modded then ``lor_highMask_mod_ite else ``lor_highMask_ite) #[x, v, mkNatLit k, hk]
  let ty ← inferType pf
  let some (_, _, rhs) := ty.eq? | return .continue
  -- The lemma's left side spells the mask `2 ^ 256 - 2 ^ k`, defeq to the literal by evaluation;
  -- its right side keeps that spelling only inside the untaken branch.
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

open Lean Meta Elab Tactic in
/-- For every hypothesis `h : ∀ k, f k < n` (a bound on every storage word, as the tree tactics state it)
and every `f t` in the goal or a hypothesis, add `h t`: `omega` does not instantiate a `∀`. -/
elab "inst_bounds" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut bounds : Array (FVarId × FVarId) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let .forallE _ dom body _ := ty | continue
    unless dom == mkConst ``Nat do continue
    let_expr LT.lt _ _ lhs _ := body | continue
    let .app (.fvar f) (.bvar 0) := lhs | continue
    bounds := bounds.push (d.fvarId, f)
  if bounds.isEmpty then return
  let mut es : Array Expr := #[← instantiateMVars (← getMainTarget)]
  for d in lctx do
    unless d.isImplementationDetail do
      es := es.push (← instantiateMVars d.type)
  let mut args : Array (FVarId × Expr) := #[]
  for e in es do
    let mut stack := #[e]
    while stack.size > 0 do
      let t := stack.back!
      stack := stack.pop
      if let .app (.fvar f) a := t then
        if !a.hasLooseBVars && bounds.any (·.2 == f) && !args.contains (f, a) then
          args := args.push (f, a)
      match t with
      | .app g x => stack := (stack.push g).push x
      | .mdata _ x => stack := stack.push x
      | _ => pure ()
  for (f, a) in args do
    for (h, f') in bounds do
      if f' == f then
        let pf := mkApp (mkFVar h) a
        let g ← getMainGoal
        let (_, g') ← (← g.assert `hbound (← inferType pf) pf).intro1P
        replaceMainGoal [g']

/-- Packed fields read back: the masks above as arithmetic, each branch condition discharged by
`omega`, words below `2 ^ 256` (by `omega`, or a hypothesis bounding every storage word, which
`solve_by_elim` applies: the tree tactics' names are hygienic), then `mul_close`. -/
macro "packed_close" : tactic => `(tactic| (
  (try inst_bounds)
  (try simp only [reduceLandLowMask] at *)
  (try simp only [reduceLorHighMask] at *)
  (try simp only [Nat.reducePow] at *)
  (try simp (disch := omega) only [if_pos] at *)
  (try simp (disch := first | omega | solve_by_elim) only [Nat.mod_eq_of_lt, add_mul_div_of_lt] at *)
  mul_close))


/-- `tree_meets_fixed` for trees with checked products and packed fields: the same steps, each
simplification allowed four million steps, each case closed by `omega`, else `packed_close`. -/
macro "tree_meets_fixed_packed" "[" ds:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  seqTactics (#[← `(tactic| intro args s iargs pre hl hargs hs hdec hst ht hreq hinv)] ++
    (← treeMeetsStepsWith ds (← `(tactic| first | omega | packed_close)) true))

end SolidCore.Spec
