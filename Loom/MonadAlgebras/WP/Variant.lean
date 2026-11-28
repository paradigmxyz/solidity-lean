import Loom.MonadAlgebras.WP.Basic

/-!
# Loops with an invariant and a variant, in any monad

Loom's unbounded loop (`Loop.forIn.loop`) is a `partial_fixpoint`, so it needs a monad
that can diverge (`CCPO`, `MonoBind`), and its total-correctness rule
(`TotalCorrectness.repeat_inv`) an algebra that sends divergence to `⊥`. A monad without
divergence, such as a state program that fails with data, runs a loop for a number of
iterations it is given. `Loop.bounded exhaust f fuel b` runs `f` from `b` until it returns
`done`, at most `fuel` times, and runs `exhaust` on what it reached if it never did.

`triple_bounded` is the total-correctness rule: an invariant that each step keeps, and a
natural-number variant that each step that continues decreases, give the loop's triple once
the fuel exceeds the initial variant, whatever `exhaust` does, since the loop then never
reaches it. `triple_while` is the same rule for a `while` loop with a condition and a body.
`bounded_eq_of_variant` says that such a loop does not depend on its fuel or `exhaust`.
-/

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] {β : Type u} {l : Type u}

/-- At most `fuel` iterations of `f` from `b`; `exhaust` on what is reached if `f` never
returned `done`. -/
def Loop.bounded (exhaust : β → m β) (f : β → m (ForInStep β)) : Nat → β → m β
  | 0, b => exhaust b
  | n + 1, b => do
    match ← f b with
    | .done b => pure b
    | .yield b => Loop.bounded exhaust f n b

/-- A `while` loop: while `cond` holds, run `body`, at most `fuel` times. -/
def Loop.whileBounded (exhaust : β → m β) (cond : β → Bool) (body : β → m β)
    (fuel : Nat) (b : β) : m β :=
  Loop.bounded exhaust (fun b => if cond b then ForInStep.yield <$> body b else pure (.done b))
    fuel b

section
variable [CompleteLattice l] [MAlgOrdered m l]

/-- Total correctness of a bounded loop: an invariant each step keeps and a variant each
continuing step decreases give the triple once the fuel exceeds the variant. -/
theorem triple_bounded (exhaust : β → m β) (f : β → m (ForInStep β))
    (inv : β → l) (doneWith : β → l) (measure : β → Nat)
    (hstep : ∀ b, triple (inv b) (f b) (fun
      | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
      | .done b' => inv b' ⊓ doneWith b')) :
    ∀ fuel init, measure init < fuel →
      triple (inv init) (Loop.bounded exhaust f fuel init) (fun b => inv b ⊓ doneWith b) := by
  intro fuel
  induction fuel with
  | zero => intro _ h; omega
  | succ n ih =>
    intro init hlt
    simp only [triple, Loop.bounded, wp_bind]
    apply le_trans (hstep init)
    apply wp_cons
    rintro (b' | b')
    · simp only [wp_pure]; exact le_refl _
    · simp only [pure_intro_l]
      intro hm
      exact ih b' (by omega)

/-- Total correctness of a bounded `while` loop: the body keeps the invariant and decreases
the variant while the condition holds; the loop ends where the invariant holds and the
condition does not. -/
theorem triple_while (exhaust : β → m β) (cond : β → Bool) (body : β → m β)
    (inv : β → l) (measure : β → Nat)
    (hbody : ∀ b, cond b = true →
      triple (inv b) (body b) (fun b' => inv b' ⊓ ⌜measure b' < measure b⌝))
    (fuel : Nat) (init : β) (hfuel : measure init < fuel) :
    triple (inv init) (Loop.whileBounded exhaust cond body fuel init)
      (fun b => inv b ⊓ ⌜cond b = false⌝) := by
  apply triple_bounded exhaust _ inv (fun b => ⌜cond b = false⌝) measure _ fuel init hfuel
  intro b
  by_cases hc : cond b = true
  · simp only [hc, if_true, triple, wp_map]
    exact hbody b hc
  · have hc' : cond b = false := by simpa using hc
    simp only [hc', triple, Bool.false_eq_true, if_false]
    rw [wp_pure]
    simp [LE.pure, hc']

end

/-- A loop whose variant decreases does not depend on its fuel past the variant. -/
theorem bounded_eq_of_variant (exhaust exhaust' : β → m β) (f : β → m (ForInStep β))
    (good : β → Prop) (measure : β → Nat)
    (hstep : ∀ b, good b → ∃ r : ForInStep β, f b = pure r ∧
      match r with | .yield b' => good b' ∧ measure b' < measure b | .done _ => True) :
    ∀ fuel fuel' b, good b → measure b < fuel → measure b < fuel' →
      Loop.bounded exhaust f fuel b = Loop.bounded exhaust' f fuel' b := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ n ih =>
    intro fuel' b hg h h'
    cases fuel' with
    | zero => omega
    | succ n' =>
      obtain ⟨r, hr, hgood⟩ := hstep b hg
      simp only [Loop.bounded, hr, pure_bind]
      cases r with
      | done b' => rfl
      | yield b' =>
        exact ih n' b' hgood.1 (by have := hgood.2; omega) (by have := hgood.2; omega)
