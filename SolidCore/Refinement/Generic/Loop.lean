import SolidCore.Refinement.Generic.SourceStmt
import SolidCore.Solidity.FuelMonotonicity

/-!
# Loops of SolidCore under ranking certificates

The generic source stage erases loop-free statements (`eraseStmt`, `eval_stmt`). This file adds
what a loop needs: a **ranking certificate** checked by the kernel, and the theorem that a loop with
one ends, at every fuel from a bound the certificate gives, in an end its certificate names.

A certificate of `for (init; cond; post) body` (`ForCert`) or `while (cond) body` (`WhileCert`)
is an invariant `Inv` of the runtime at the loop's header, a measure `rank` into `Nat`, a body fuel
`k` and the property `Q` of the loop's result. From every runtime of `Inv` the condition must
evaluate; when it is false, or reverts, or the body breaks, returns or reverts, the result meets
`Q`; when an iteration goes on, it must come back to `Inv` with a strictly smaller rank. Nothing
else is assumed: the condition, the body and `post` run in SolidCore's interpreter
(`Stmt.eval`), and the rank's fall is part of the obligation, so a certificate whose rank does not
fall is not one.

* `evalFor_of_cert`, `evalWhile_of_cert`: from a runtime of `Inv` with rank below `N`, the loop
  ends in a result meeting `Q` at every fuel from `N + k` on. The bound is linear in the rank:
  each iteration spends one unit of the loop's fuel, and SolidCore's fuel monotonicity
  (`Stmt.eval_fuel_mono`) keeps the body's result when later iterations run it with less fuel
  than the first.
* `forLoop_of_cert`, `whileLoop_of_cert`: the same of the statements, the `for` loop's scope and
  `init` included.
* `evalFor_never`, `forLoop_never`: the converse control. A loop that makes no progress (from
  every runtime of `P` the condition holds and a finished iteration comes back to `P`) finishes at
  no fuel at all: no ranking certificate exists for it, and no fuel ends it.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source
open EvmCompiler.Simulation (Interaction)

theorem noFuelStop_done {α : Type} (a : α) :
    SolI.NoFuelStop (Interaction.done (.ok a) : SolI α) :=
  Interaction.AllDone.done (by intro h; cases h)

/-- A statement that ends at some fuel ends the same way at every larger fuel. -/
theorem eval_mono {n m : Nat} (hnm : n ≤ m) {tbl : FunctionTable} {ctx : Context} {rt : Runtime}
    {s : Stmt} {r : Result} (h : Stmt.eval n tbl ctx rt s = .done (.ok r)) :
    Stmt.eval m tbl ctx rt s = .done (.ok r) := by
  rw [Stmt.eval_fuel_mono hnm (by rw [h]; exact noFuelStop_done r), h]

/-- A bind that ends had a prefix that ended. -/
theorem bind_eq_done {α β : Type} {t : SolI α} {k : α → SolI β} {b : β}
    (h : (t >>= k) = .done (.ok b)) : ∃ a, t = .done (.ok a) ∧ k a = .done (.ok b) := by
  cases t with
  | done o =>
    cases o with
    | ok a => exact ⟨a, rfl, h⟩
    | error e => cases h
  | request q r => cases h

/-- What the condition of a loop does from the header runtime `rt`: it evaluates, and when it is
false or reverts the result meets `Q`, while when it holds the runtime after it meets `Go`. -/
def CondStep (ctx : Context) (cond : Expr) (rt : Runtime) (Q : Result → Prop)
    (Go : Runtime → Prop) : Prop :=
  ∃ c, (Expr.eval ctx rt cond).caught = .done (.ok c) ∧
    match c with
    | .error err => Q (.reverted rt err)
    | .ok (v, rt') =>
      match v.expectWord with
      | .error err => Q (.reverted rt' err)
      | .ok w => if wordTruthy w then Go rt' else Q (.normal rt')

/-- What the rest of a `for` iteration does after the body's result: `post` runs (fuel `k`) after a
normal or `continue` end and either comes back to `Next` or ends the loop meeting `Q`; a `break`
ends the loop normally, and every other end of the body is the loop's. -/
def ForRest (k : Nat) (tbl : FunctionTable) (ctx : Context) (post : Stmt)
    (Next : Runtime → Prop) (Q : Result → Prop) : Result → Prop
  | .normal rb => ∃ r2, Stmt.eval k tbl ctx rb post = .done (.ok r2) ∧
      match r2 with
      | .normal rp => Next rp
      | r => Q r
  | .continued rb => ∃ r2, Stmt.eval k tbl ctx rb post = .done (.ok r2) ∧
      match r2 with
      | .normal rp => Next rp
      | r => Q r
  | .broke rb => Q (.normal rb)
  | .returned rt vs => Q (.returned rt vs)
  | .selfdestructed rt => Q (.selfdestructed rt)
  | .reverted rt e => Q (.reverted rt e)

/-- **A ranking certificate of `for (…; cond; post) body`**: from every runtime of `Inv`, the
condition evaluates; an iteration runs its body and `post` within fuel `k` and either ends the
loop meeting `Q` or comes back to `Inv` with a strictly smaller `rank`. -/
structure ForCert (k : Nat) (tbl : FunctionTable) (ctx : Context) (cond : Expr) (post body : Stmt)
    (Inv : Runtime → Prop) (rank : Runtime → Nat) (Q : Result → Prop) : Prop where
  step : ∀ rt, Inv rt → CondStep ctx cond rt Q (fun rt' =>
    ∃ r1, Stmt.eval k tbl ctx rt' body = .done (.ok r1) ∧
      ForRest k tbl ctx post (fun rp => Inv rp ∧ rank rp < rank rt) Q r1)

/-- **A `for` loop with a ranking certificate ends**, from a runtime of the invariant whose rank is
below `N`, at every fuel from `N + k` on, in a result meeting `Q`. -/
theorem evalFor_of_cert {k : Nat} {tbl : FunctionTable} {ctx : Context} {cond : Expr}
    {post body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat} {Q : Result → Prop}
    (h : ForCert k tbl ctx cond post body Inv rank Q) :
    ∀ N rt, Inv rt → rank rt < N → ∀ fuel, N + k ≤ fuel →
      ∃ r, Stmt.evalFor fuel tbl ctx rt cond post body = .done (.ok r) ∧ Q r := by
  intro N
  induction N with
  | zero => intro rt _ hr; omega
  | succ N ih =>
    intro rt hinv hr fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨c, hc, hstep⟩ := h.step rt hinv
    simp only [Stmt.evalFor]
    rw [hc, bind_done_ok]
    rcases c with err | ⟨v, rt'⟩
    · exact ⟨_, rfl, hstep⟩
    dsimp only at hstep ⊢
    rcases hv : v.expectWord with err | w <;> simp only [hv] at hstep ⊢
    · exact ⟨_, rfl, hstep⟩
    by_cases ht : wordTruthy w = true
    · rw [if_pos ht] at hstep ⊢
      obtain ⟨r1, hb, hrest⟩ := hstep
      rw [eval_mono (by omega) hb, bind_done_ok]
      rcases r1 with rb | ⟨rt1, vs⟩ | rt1 | ⟨rt1, e⟩ | rb | rb <;> dsimp only [ForRest] at hrest ⊢
      · obtain ⟨r2, hp, hn⟩ := hrest
        rw [eval_mono (by omega) hp, bind_done_ok]
        rcases r2 with rp | ⟨rt2, vs⟩ | rt2 | ⟨rt2, e⟩ | rt2 | rt2 <;> dsimp only at hn ⊢
        · exact ih rp hn.1 (by omega) f (by omega)
        all_goals exact ⟨_, rfl, hn⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · obtain ⟨r2, hp, hn⟩ := hrest
        rw [eval_mono (by omega) hp, bind_done_ok]
        rcases r2 with rp | ⟨rt2, vs⟩ | rt2 | ⟨rt2, e⟩ | rt2 | rt2 <;> dsimp only at hn ⊢
        · exact ih rp hn.1 (by omega) f (by omega)
        all_goals exact ⟨_, rfl, hn⟩
    · rw [if_neg ht] at hstep ⊢
      exact ⟨_, rfl, hstep⟩

/-- **The `for` statement with a ranking certificate ends**: its scope opens, `init` runs (fuel
`k0`) to a runtime of the invariant, and from `rank + k + 1` more fuel on, the loop ends meeting
`Q`, its scope closed. -/
theorem forLoop_of_cert {k k0 : Nat} {tbl : FunctionTable} {ctx : Context} {init : Stmt}
    {cond : Expr} {post body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat}
    {Q : Result → Prop} (h : ForCert k tbl ctx cond post body Inv rank Q) {rt rt1 : Runtime}
    (hinit : Stmt.eval k0 tbl ctx rt.pushScope init = .done (.ok (.normal rt1))) (hinv : Inv rt1)
    (fuel : Nat) (hf : rank rt1 + 1 + k + 1 ≤ fuel) (hk0 : k0 + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel tbl ctx rt (.forLoop init cond post body) =
      .done (.ok (r.mapRuntime Runtime.popScope)) ∧ Q r := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨r, hr, hq⟩ := evalFor_of_cert h (rank rt1 + 1) rt1 hinv (by omega) f (by omega)
  refine ⟨r, ?_, hq⟩
  simp only [Stmt.eval]
  rw [eval_mono (by omega) hinit, bind_done_ok]
  dsimp only
  rw [hr, bind_done_ok]
  rfl

/-- What the rest of a `while` iteration does after the body's result. -/
def WhileRest (Next : Runtime → Prop) (Q : Result → Prop) : Result → Prop
  | .normal rb => Next rb
  | .continued rb => Next rb
  | .broke rb => Q (.normal rb)
  | .returned rt vs => Q (.returned rt vs)
  | .selfdestructed rt => Q (.selfdestructed rt)
  | .reverted rt e => Q (.reverted rt e)

/-- **A ranking certificate of `while (cond) body`.** -/
structure WhileCert (k : Nat) (tbl : FunctionTable) (ctx : Context) (cond : Expr) (body : Stmt)
    (Inv : Runtime → Prop) (rank : Runtime → Nat) (Q : Result → Prop) : Prop where
  step : ∀ rt, Inv rt → CondStep ctx cond rt Q (fun rt' =>
    ∃ r1, Stmt.eval k tbl ctx rt' body = .done (.ok r1) ∧
      WhileRest (fun rb => Inv rb ∧ rank rb < rank rt) Q r1)

/-- **A `while` loop with a ranking certificate ends**, at every fuel from `N + k` on. -/
theorem evalWhile_of_cert {k : Nat} {tbl : FunctionTable} {ctx : Context} {cond : Expr}
    {body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat} {Q : Result → Prop}
    (h : WhileCert k tbl ctx cond body Inv rank Q) :
    ∀ N rt, Inv rt → rank rt < N → ∀ fuel, N + k ≤ fuel →
      ∃ r, Stmt.evalWhile fuel tbl ctx rt cond body = .done (.ok r) ∧ Q r := by
  intro N
  induction N with
  | zero => intro rt _ hr; omega
  | succ N ih =>
    intro rt hinv hr fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨c, hc, hstep⟩ := h.step rt hinv
    simp only [Stmt.evalWhile]
    rw [hc, bind_done_ok]
    rcases c with err | ⟨v, rt'⟩
    · exact ⟨_, rfl, hstep⟩
    dsimp only at hstep ⊢
    rcases hv : v.expectWord with err | w <;> simp only [hv] at hstep ⊢
    · exact ⟨_, rfl, hstep⟩
    by_cases ht : wordTruthy w = true
    · rw [if_pos ht] at hstep ⊢
      obtain ⟨r1, hb, hrest⟩ := hstep
      rw [eval_mono (by omega) hb, bind_done_ok]
      rcases r1 with rb | ⟨rt1, vs⟩ | rt1 | ⟨rt1, e⟩ | rb | rb <;> dsimp only [WhileRest] at hrest ⊢
      · exact ih rb hrest.1 (by omega) f (by omega)
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ⟨_, rfl, hrest⟩
      · exact ih rb hrest.1 (by omega) f (by omega)
    · rw [if_neg ht] at hstep ⊢
      exact ⟨_, rfl, hstep⟩

theorem whileLoop_of_cert {k : Nat} {tbl : FunctionTable} {ctx : Context} {cond : Expr}
    {body : Stmt} {Inv : Runtime → Prop} {rank : Runtime → Nat} {Q : Result → Prop}
    (h : WhileCert k tbl ctx cond body Inv rank Q) {rt : Runtime} (hinv : Inv rt) (fuel : Nat)
    (hf : rank rt + 1 + k + 1 ≤ fuel) :
    ∃ r, Stmt.eval fuel tbl ctx rt (.whileLoop cond body) = .done (.ok r) ∧ Q r := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [Stmt.eval]
  exact evalWhile_of_cert h (rank rt + 1) rt hinv (by omega) f (by omega)

/-! ## A loop without progress ends at no fuel -/

theorem wordTruthy_norm (w : Nat) :
    wordTruthy (SolidCore.Solidity.Shared.norm w) = wordTruthy w := by
  simp [wordTruthy, SolidCore.Solidity.Shared.norm]

/-- **A `for` loop that makes no progress finishes at no fuel.** From every runtime of `P` the
condition holds and some fuel finishes the body and `post` normally, back in `P`. -/
theorem evalFor_never {tbl : FunctionTable} {ctx : Context} {cond : Expr} {post body : Stmt}
    (P : Runtime → Prop)
    (h : ∀ rt, P rt → ∃ w rt', (Expr.eval ctx rt cond).caught = .done (.ok (.ok (.word w, rt'))) ∧
      wordTruthy w = true ∧ ∃ k rb, Stmt.eval k tbl ctx rt' body = .done (.ok (.normal rb)) ∧
        ∃ rp, Stmt.eval k tbl ctx rb post = .done (.ok (.normal rp)) ∧ P rp) :
    ∀ fuel rt, P rt → ∀ r, Stmt.evalFor fuel tbl ctx rt cond post body ≠ .done (.ok r) := by
  intro fuel
  induction fuel with
  | zero => intro rt _ r hr; simp only [Stmt.evalFor] at hr; cases hr
  | succ f ih =>
    intro rt hp r hr
    obtain ⟨w, rt', hc, ht, k, rb, hb, rp, hpo, hp'⟩ := h rt hp
    simp only [Stmt.evalFor] at hr
    rw [hc, bind_done_ok] at hr
    simp only [Value.expectWord, wordTruthy_norm, ht, ite_true] at hr
    obtain ⟨r1, hb1, hr⟩ := bind_eq_done hr
    have e1 : r1 = .normal rb := by
      have := (eval_mono (Nat.le_max_left f k) hb1).symm.trans (eval_mono (Nat.le_max_right f k) hb)
      cases this; rfl
    subst e1
    obtain ⟨r2, hp2, hr⟩ := bind_eq_done hr
    have e2 : r2 = .normal rp := by
      have := (eval_mono (Nat.le_max_left f k) hp2).symm.trans (eval_mono (Nat.le_max_right f k) hpo)
      cases this; rfl
    subst e2
    exact ih rp hp' r hr

/-- **The `for` statement of a loop without progress finishes at no fuel.** -/
theorem forLoop_never {tbl : FunctionTable} {ctx : Context} {init : Stmt} {cond : Expr}
    {post body : Stmt} (P : Runtime → Prop)
    (h : ∀ rt, P rt → ∃ w rt', (Expr.eval ctx rt cond).caught = .done (.ok (.ok (.word w, rt'))) ∧
      wordTruthy w = true ∧ ∃ k rb, Stmt.eval k tbl ctx rt' body = .done (.ok (.normal rb)) ∧
        ∃ rp, Stmt.eval k tbl ctx rb post = .done (.ok (.normal rp)) ∧ P rp)
    {rt rt1 : Runtime} {k0 : Nat}
    (hinit : Stmt.eval k0 tbl ctx rt.pushScope init = .done (.ok (.normal rt1))) (hp : P rt1) :
    ∀ fuel r, Stmt.eval fuel tbl ctx rt (.forLoop init cond post body) ≠ .done (.ok r) := by
  intro fuel r hr
  cases fuel with
  | zero => simp only [Stmt.eval] at hr; cases hr
  | succ f =>
    simp only [Stmt.eval] at hr
    obtain ⟨r0, h0, hr⟩ := bind_eq_done hr
    have e0 : r0 = .normal rt1 := by
      have := (eval_mono (Nat.le_max_left f k0) h0).symm.trans (eval_mono (Nat.le_max_right f k0) hinit)
      cases this; rfl
    subst e0
    obtain ⟨r1, h1, -⟩ := bind_eq_done hr
    exact evalFor_never P h f rt1 hp r1 h1

/-- info: 'SolidCore.Refinement.Generic.Loop.forLoop_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forLoop_of_cert

/-- info: 'SolidCore.Refinement.Generic.Loop.forLoop_never' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forLoop_never

end SolidCore.Refinement.Generic.Loop
