import SolarTV.CutPointHoare

/-! # Termination and resource certificates through cut points

`CutPoint.ends_of_segments` proves that a machine ends from a Nat rank that every segment
between cut points lowers. This module makes that the reusable termination checker the
certified pipeline needs, in four parts.

* **Well-founded ranks** (`ends_of_segments_wf`, `ends_of_reach`): any well-founded relation
  on any type of ranks, so nested loops take lexicographic ranks (`Prod.Lex`) and recursion
  takes a measure on the call stack. The ranking certificate is data (an invariant and a rank
  per cut point, emitted by solar's `inferred.py` from what `solar-verify --show-inferred`
  infers); nothing here trusts it: each segment must be shown to end at a cut point meeting the
  invariant with a lower rank, or in a result meeting the postcondition. A segment that is stuck
  or runs out of its fuel proves nothing (`SegEnds` is `False` there), so a certificate whose
  rank does not fall fails by mismatch (`Negative.flat_rejected`).

* **Compositional total contracts** (`Reaches`, `Reaches.trans`, `Reaches.of_wf`): a total
  contract `Reaches step Pre Q` says every configuration meeting `Pre` runs, in finitely many
  steps, to one meeting `Q` (an internal call's entry to its return to the caller) or to an end
  meeting `Post`. Contracts compose, and a recursive function's contract follows from its
  body's under a well-founded recursion measure (`Reaches.of_wf`): the body may use the
  contract at every call whose measure is lower.

* **Explicit step bounds** (`ends_within`, `ends_within_start`): when every segment of the
  certificate has at most `K` steps, a run from a cut point of rank `r` ends within
  `(r + 1) * K` steps; a bound derived from the ranking, not a chosen fuel.

* **Resources** (`runGas`, `gas_ends`, `runGas_done_run`): a metered run charges each step
  `cost x` before it takes it and fails with `oog` when the gas left is lower, as the EVM does.
  When every segment of the certificate costs at most `C`, a metered run from a cut point of
  rank `r` with gas at least `(r + 1) * C` never runs out of gas and ends in a result meeting
  `Post` (`gas_ends`); and a metered run that ends gives the result the unmetered run gives
  (`runGas_done_run`), so the resource bound is a separate theorem from the gas-insensitive
  behaviour, and the premise on the gas is a number, not an assumption of success.
  `Negative.oog_below` shows the bound is not vacuous: below it a metered run does run out.
-/

namespace SolarTV.CutPoint

universe u v w

variable {σ : Type u} {R : Type v}

/-- A segment's obligation is decidable when its parts are, so a certificate on concrete
configurations is checked by evaluation. -/
instance SegEnds.decidable {Inv : σ → Prop} {Post : R → Prop} {below : σ → Prop}
    [DecidablePred Inv] [DecidablePred Post] [DecidablePred below] :
    ∀ s : Seg R σ, Decidable (SegEnds Inv Post below s)
  | .done r => inferInstanceAs (Decidable (Post r))
  | .cut y => inferInstanceAs (Decidable (Inv y ∧ below y))
  | .stuck => isFalse id
  | .fuel => isFalse id

/-! ## Segment lengths -/

section Lengths

variable {step : Step σ R} {cut : σ → Bool}

/-- A segment with `k` steps of fuel that reaches a cut point ran at most `k` steps to it. -/
theorem seg_cut_le : ∀ {k : Nat} {x y : σ}, seg step cut k x = .cut y →
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ ∀ n, run step (n + j) x = run step n y ∧ steps step (n + j) x = steps step n y
  | 0, _, _, h => by cases h
  | k + 1, x, y, h => by
    simp only [seg] at h
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r => rw [e] at h; cases h
      | inr z =>
        rw [e] at h
        simp only at h
        by_cases c : cut z = true
        · simp only [c, ↓reduceIte] at h
          cases h
          refine ⟨1, Nat.le_refl 1, by omega, fun n => ⟨?_, ?_⟩⟩ <;> simp only [run, steps, e]
        · simp only [c] at h
          obtain ⟨j, pos, le, runs⟩ := seg_cut_le h
          refine ⟨j + 1, by omega, by omega, fun n => ?_⟩
          rw [← Nat.add_assoc]
          simp only [run, steps, e]
          exact runs n

/-- A segment with `k` steps of fuel that ends ran at most `k` steps to its result. -/
theorem seg_done_le : ∀ {k : Nat} {x : σ} {r : R}, seg step cut k x = .done r →
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ ∀ n, run step (n + j) x = some r
  | 0, _, _, h => by cases h
  | k + 1, x, r, h => by
    simp only [seg] at h
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r' =>
        rw [e] at h
        cases h
        exact ⟨1, Nat.le_refl 1, by omega, fun n => by simp only [run, e]⟩
      | inr z =>
        rw [e] at h
        simp only at h
        by_cases c : cut z = true
        · simp only [c, ↓reduceIte] at h; cases h
        · simp only [c] at h
          obtain ⟨j, pos, le, runs⟩ := seg_done_le h
          refine ⟨j + 1, by omega, by omega, fun n => ?_⟩
          rw [← Nat.add_assoc]
          simp only [run, e]
          exact runs n

end Lengths

/-! ## Well-founded ranks -/

/-- **Total correctness through cut points under any well-founded rank**: lexicographic ranks
for nested loops, stack measures for recursion. -/
theorem ends_of_segments_wf {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    {α : Sort w} {lt : α → α → Prop} (wf : WellFounded lt) (rank : σ → α)
    (segment : ∀ x, Inv x → ∃ k, SegEnds Inv Post (fun y => lt (rank y) (rank x)) (seg step cut k x)) :
    ∀ x, Inv x → ∃ n r, run step n x = some r ∧ Post r := by
  intro x
  induction x using (InvImage.wf rank wf).induction with
  | h x ih =>
    intro inv
    obtain ⟨k, hk⟩ := segment x inv
    cases hs : seg step cut k x with
    | fuel | stuck => rw [hs] at hk; exact hk.elim
    | done a =>
      rw [hs] at hk
      obtain ⟨j, _, runs⟩ := seg_done hs
      exact ⟨0 + j, a, runs 0, hk⟩
    | cut y =>
      rw [hs] at hk
      obtain ⟨iy, lt'⟩ := hk
      obtain ⟨j, _, runs⟩ := seg_cut hs
      obtain ⟨n, r, ran, post⟩ := ih y lt' iy
      exact ⟨n + j, r, by rw [(runs n).1]; exact ran, post⟩

/-! ## Compositional total contracts -/

/-- **A total contract**: from every configuration meeting `Pre`, the machine reaches, in
finitely many steps, a configuration meeting `Q` or an end meeting `Post`. An internal call's
contract has the callee's entry as `Pre` and the caller's return configuration as `Q`. -/
def Reaches (step : Step σ R) (Pre Q : σ → Prop) (Post : R → Prop) : Prop :=
  ∀ x, Pre x → (∃ n r, run step n x = some r ∧ Post r) ∨ ∃ j y, steps step j x = some (.inr y) ∧ Q y

theorem steps_add {step : Step σ R} : ∀ (i j : Nat) (x : σ) (y : σ),
    steps step i x = some (.inr y) → steps step (i + j) x = steps step j y
  | 0, j, x, y, h => by simp only [steps] at h; cases h; simp
  | i + 1, j, x, y, h => by
    rw [Nat.add_right_comm]
    simp only [steps] at h ⊢
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r => rw [e] at h; cases h
      | inr z => rw [e] at h; exact steps_add i j z y h

theorem run_add {step : Step σ R} (i n : Nat) (x y : σ) (h : steps step i x = some (.inr y)) :
    run step (i + n) x = run step n y := by
  rw [run_eq_steps, run_eq_steps, steps_add i n x y h]

/-- Total contracts compose. -/
theorem Reaches.trans {step : Step σ R} {P Q S : σ → Prop} {Post : R → Prop}
    (h1 : Reaches step P Q Post) (h2 : Reaches step Q S Post) : Reaches step P S Post := by
  intro x hx
  rcases h1 x hx with e | ⟨i, y, hy, qy⟩
  · exact Or.inl e
  rcases h2 y qy with ⟨n, r, ran, post⟩ | ⟨j, z, hz, sz⟩
  · exact Or.inl ⟨i + n, r, by rw [run_add i n x y hy]; exact ran, post⟩
  · exact Or.inr ⟨i + j, z, by rw [steps_add i j x y hy]; exact hz, sz⟩

/-- A total contract whose target is the end itself is termination. -/
theorem Reaches.ends {step : Step σ R} {P : σ → Prop} {Post : R → Prop}
    (h : Reaches step P (fun _ => False) Post) : ∀ x, P x → ∃ n r, run step n x = some r ∧ Post r :=
  fun x hx => (h x hx).resolve_right (fun ⟨_, _, _, f⟩ => f)

/-- **Recursion**: a contract follows from its body's, when the body may use the contract at
every configuration of lower measure (the recursive calls), for a well-founded measure. -/
theorem Reaches.of_wf {step : Step σ R} {P Q : σ → Prop} {Post : R → Prop} {α : Sort w}
    {lt : α → α → Prop} (wf : WellFounded lt) (μ : σ → α)
    (body : ∀ x, P x → Reaches step (fun x' => P x' ∧ lt (μ x') (μ x)) Q Post →
      (∃ n r, run step n x = some r ∧ Post r) ∨ ∃ j y, steps step j x = some (.inr y) ∧ Q y) :
    Reaches step P Q Post := by
  intro x
  induction x using (InvImage.wf μ wf).induction with
  | h x ih => exact fun hx => body x hx (fun x' ⟨px', lt'⟩ => ih x' lt' px')

/-- Total correctness from contracts: when every configuration of the invariant reaches an end
meeting `Post` or another configuration of the invariant with a lower rank (a segment, or a
segment that runs a callee through its contract), every run from the invariant ends. Unlike
`ends_of_segments_wf`, the steps to the next configuration need not stop at the first cut
point, so a caller's segment may run a whole callee. -/
theorem ends_of_reach {step : Step σ R} {Inv : σ → Prop} {Post : R → Prop} {α : Sort w}
    {lt : α → α → Prop} (wf : WellFounded lt) (rank : σ → α)
    (segment : ∀ x, Inv x → (∃ n r, run step n x = some r ∧ Post r) ∨
      ∃ j y, steps step j x = some (.inr y) ∧ Inv y ∧ lt (rank y) (rank x)) :
    ∀ x, Inv x → ∃ n r, run step n x = some r ∧ Post r := by
  intro x
  induction x using (InvImage.wf rank wf).induction with
  | h x ih =>
    intro inv
    rcases segment x inv with e | ⟨i, y, hy, iy, lt'⟩
    · exact e
    obtain ⟨n, r, ran, post⟩ := ih y lt' iy
    exact ⟨i + n, r, by rw [run_add i n x y hy]; exact ran, post⟩

/-! ## Segments to a callee's return -/

/-- A segment of a callee that ends as its total contract asks: in a result meeting `Post`
(a revert, say), at a cut point of its invariant with a lower rank, or at a configuration
meeting `Q` (the caller resumed). Stuck and out of fuel prove nothing. -/
def SegReaches (Inv Q : σ → Prop) (Post : R → Prop) (below : σ → Prop) : Seg R σ → Prop
  | .done r => Post r
  | .cut y => (Inv y ∧ below y) ∨ Q y
  | .stuck => False
  | .fuel => False

/-- A weaker invariant, target and postcondition. -/
theorem SegReaches.mono {Inv Inv' Q Q' : σ → Prop} {Post Post' : R → Prop} {below : σ → Prop}
    (hi : ∀ y, Inv y → Inv' y) (hq : ∀ y, Q y → Q' y) (hp : ∀ r, Post r → Post' r) :
    ∀ {s : Seg R σ}, SegReaches Inv Q Post below s → SegReaches Inv' Q' Post' below s
  | .done _, h => hp _ h
  | .cut _, h => h.elim (fun ⟨a, b⟩ => Or.inl ⟨hi _ a, b⟩) (fun q => Or.inr (hq _ q))
  | .stuck, h | .fuel, h => h

/-- **A callee's total contract from its segments**: when every segment from the invariant ends
in a result meeting `Post`, at the invariant with a lower rank, or at `Q`, every configuration of
the invariant reaches `Q` or such a result. -/
theorem reaches_of_segments {step : Step σ R} {cut : σ → Bool} {Inv Q : σ → Prop}
    {Post : R → Prop} (rank : σ → Nat)
    (segment : ∀ x, Inv x → ∃ k, SegReaches Inv Q Post (fun y => rank y < rank x) (seg step cut k x)) :
    Reaches step Inv Q Post := by
  intro x
  induction h : rank x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    intro inv
    obtain ⟨k, hk⟩ := segment x inv
    cases hs : seg step cut k x with
    | fuel | stuck => rw [hs] at hk; exact hk.elim
    | done a =>
      rw [hs] at hk
      obtain ⟨j, _, runs⟩ := seg_done hs
      exact Or.inl ⟨0 + j, a, runs 0, hk⟩
    | cut y =>
      rw [hs] at hk
      obtain ⟨j, _, runs⟩ := seg_cut hs
      have hy : steps step j x = some (.inr y) := by
        have := (runs 0).2
        simpa [steps] using this
      rcases hk with ⟨iy, lt⟩ | qy
      · rcases ih (rank y) (h ▸ lt) y rfl iy with ⟨n, r, ran, post⟩ | ⟨i, z, hz, qz⟩
        · exact Or.inl ⟨j + n, r, by rw [run_add j n x y hy]; exact ran, post⟩
        · exact Or.inr ⟨j + i, z, by rw [steps_add j i x y hy]; exact hz, qz⟩
      · exact Or.inr ⟨j, y, hy, qy⟩

/-- The same from a first configuration that need not be a cut point. -/
theorem reaches_of_start {step : Step σ R} {cut : σ → Bool} {Inv Q : σ → Prop}
    {Post : R → Prop} (rank : σ → Nat) {x₀ : σ}
    (start : ∃ k, SegReaches Inv Q Post (fun _ => True) (seg step cut k x₀))
    (segment : ∀ x, Inv x → ∃ k, SegReaches Inv Q Post (fun y => rank y < rank x) (seg step cut k x)) :
    (∃ n r, run step n x₀ = some r ∧ Post r) ∨ ∃ j y, steps step j x₀ = some (.inr y) ∧ Q y :=
  Reaches.trans (P := (· = x₀)) (Q := fun y => Inv y ∨ Q y)
    (fun x hx => by
      subst hx
      obtain ⟨k, hk⟩ := start
      cases hs : seg step cut k x with
      | fuel | stuck => rw [hs] at hk; exact hk.elim
      | done a =>
        rw [hs] at hk
        obtain ⟨j, _, runs⟩ := seg_done hs
        exact Or.inl ⟨0 + j, a, runs 0, hk⟩
      | cut y =>
        rw [hs] at hk
        obtain ⟨j, _, runs⟩ := seg_cut hs
        have hy : steps step j x = some (.inr y) := by simpa [steps] using (runs 0).2
        exact Or.inr ⟨j, y, hy, hk.elim (fun h => Or.inl h.1) Or.inr⟩)
    (fun y hy => hy.elim (reaches_of_segments rank segment y)
      (fun q => Or.inr ⟨0, y, rfl, q⟩)) x₀ rfl

/-- info: 'SolarTV.CutPoint.reaches_of_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reaches_of_start

/-! ## Explicit step bounds -/

/-- **A step bound from the ranking**: when every segment of the certificate takes at most `K`
steps of fuel, a run from a cut point of rank `r` ends within `(r + 1) * K` steps. -/
theorem ends_within {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    (rank : σ → Nat) (K : Nat)
    (segment : ∀ x, Inv x → SegEnds Inv Post (fun y => rank y < rank x) (seg step cut K x)) :
    ∀ x, Inv x → ∃ r, run step ((rank x + 1) * K) x = some r ∧ Post r := by
  intro x
  induction h : rank x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    intro inv
    have hk := segment x inv
    cases hs : seg step cut K x with
    | fuel | stuck => rw [hs] at hk; exact hk.elim
    | done a =>
      rw [hs] at hk
      obtain ⟨j, _, le, runs⟩ := seg_done_le hs
      refine ⟨a, ?_, hk⟩
      have := runs ((m + 1) * K - j)
      rw [show (m + 1) * K - j + j = (m + 1) * K by
        have : K ≤ (m + 1) * K := Nat.le_mul_of_pos_left K (Nat.succ_pos m)
        omega] at this
      exact this
    | cut y =>
      rw [hs] at hk
      obtain ⟨iy, lt⟩ := hk
      obtain ⟨j, _, le, runs⟩ := seg_cut_le hs
      obtain ⟨r, ran, post⟩ := ih (rank y) (h ▸ lt) y rfl iy
      refine ⟨r, ?_, post⟩
      have e1 := (runs ((rank y + 1) * K)).1
      rw [ran] at e1
      apply run_mono _ e1
      have : (rank y + 1) * K + K ≤ (m + 1) * K := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K (by omega)
      omega

/-- The same from a first configuration that need not be a cut point, with every rank of the
invariant at most `B`: the run ends within `(B + 2) * K` steps. -/
theorem ends_within_start {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    (rank : σ → Nat) (K B : Nat) (hB : ∀ y, Inv y → rank y ≤ B) {x₀ : σ}
    (start : SegEnds Inv Post (fun _ => True) (seg step cut K x₀))
    (segment : ∀ x, Inv x → SegEnds Inv Post (fun y => rank y < rank x) (seg step cut K x)) :
    ∃ r, run step ((B + 2) * K) x₀ = some r ∧ Post r := by
  cases hs : seg step cut K x₀ with
  | fuel | stuck => rw [hs] at start; exact start.elim
  | done a =>
    rw [hs] at start
    obtain ⟨j, _, le, runs⟩ := seg_done_le hs
    refine ⟨a, ?_, start⟩
    have := runs ((B + 2) * K - j)
    rw [show (B + 2) * K - j + j = (B + 2) * K by
      have : K ≤ (B + 2) * K := Nat.le_mul_of_pos_left K (by omega)
      omega] at this
    exact this
  | cut y =>
    rw [hs] at start
    obtain ⟨j, _, le, runs⟩ := seg_cut_le hs
    obtain ⟨r, ran, post⟩ := ends_within rank K segment y start.1
    refine ⟨r, ?_, post⟩
    have e1 := (runs ((rank y + 1) * K)).1
    rw [ran] at e1
    apply run_mono _ e1
    have : (rank y + 1) * K + K ≤ (B + 2) * K := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K (by have := hB y start.1; omega)
    omega

/-! ## Bounds along simulations -/

section Sim

universe u' v'

variable {τ : Type u'} {R' : Type v'}

/-- A segment that ends does not depend on fuel beyond what it took. -/
theorem seg_fuel_mono {step : Step σ R} {cut : σ → Bool} :
    ∀ {k k' : Nat} {x : σ}, k ≤ k' → seg step cut k x ≠ .fuel → seg step cut k' x = seg step cut k x
  | 0, _, _, _, h => absurd rfl h
  | k + 1, 0, _, le, _ => absurd le (by omega)
  | k + 1, k' + 1, x, le, h => by
    simp only [seg] at h ⊢
    cases e : step x with
    | none => rfl
    | some v =>
      cases v with
      | inl r => rfl
      | inr y =>
        simp only [e] at h
        by_cases c : cut y = true
        · simp only [c, ↓reduceIte]
        · simp only [c, Bool.false_eq_true, ↓reduceIte] at h ⊢
          exact seg_fuel_mono (by omega) h

theorem seg_eq_of_ne_fuel {step : Step σ R} {cut : σ → Bool} {k k' : Nat} {x : σ}
    (h : seg step cut k x ≠ .fuel) (h' : seg step cut k' x ≠ .fuel) :
    seg step cut k x = seg step cut k' x := by
  rcases Nat.le_total k k' with le | le
  · exact (seg_fuel_mono le h).symm
  · exact seg_fuel_mono le h'

/-- **A simulation whose target segments take at most `K'` steps**: from related
configurations, the source's segment (at some fuel) and the target's segment within `K'` steps
end alike. The certify driver's stage proofs give each target segment a literal fuel. -/
def BoundedSim (step : Step σ R) (cut : σ → Bool) (step' : Step τ R') (cut' : τ → Bool)
    (Ag : R → R' → Prop) (Rel : σ → τ → Prop) (K' : Nat) : Prop :=
  ∀ x x', Rel x x' → ∃ k, SegRel Ag Rel (seg step cut k x) (seg step' cut' K' x')

/-- **A step bound on the target from a ranking certificate on the source**: segments match one
for one, so a run of the target from a configuration related to a cut point of rank `r` ends
within `(r + 1) * K'` steps, in a result that agrees with one meeting `Post`. -/
theorem ends_within_sim {step : Step σ R} {cut : σ → Bool} {step' : Step τ R'} {cut' : τ → Bool}
    {Ag : R → R' → Prop} {Rel : σ → τ → Prop} {Inv : σ → Prop} {Post : R → Prop}
    (rank : σ → Nat) (K K' : Nat)
    (segment : ∀ x, Inv x → SegEnds Inv Post (fun y => rank y < rank x) (seg step cut K x))
    (sim : BoundedSim step cut step' cut' Ag Rel K') :
    ∀ x x', Inv x → Rel x x' →
      ∃ r', run step' ((rank x + 1) * K') x' = some r' ∧ ∃ r, Ag r r' ∧ Post r := by
  intro x
  induction h : rank x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    intro x' inv rel
    have hk := segment x inv
    obtain ⟨k, hs⟩ := sim x x' rel
    have hne : seg step cut K x ≠ .fuel := fun e => by rw [e] at hk; exact hk
    have hne' : seg step cut k x ≠ .fuel := fun e => by rw [e] at hs; exact hs
    rw [seg_eq_of_ne_fuel hne' hne] at hs
    have hK : K' ≤ (m + 1) * K' := Nat.le_mul_of_pos_left K' (Nat.succ_pos m)
    cases ha : seg step cut K x with
    | fuel | stuck => rw [ha] at hk; exact hk.elim
    | done a =>
      rw [ha] at hk hs
      cases hb : seg step' cut' K' x' with
      | done b =>
        rw [hb] at hs
        obtain ⟨j, _, le, runs⟩ := seg_done_le hb
        refine ⟨b, ?_, a, hs, hk⟩
        have := runs ((m + 1) * K' - j)
        rwa [show (m + 1) * K' - j + j = (m + 1) * K' by omega] at this
      | cut _ | stuck | fuel => rw [hb] at hs; exact hs.elim
    | cut y =>
      rw [ha] at hk hs
      obtain ⟨iy, lt⟩ := hk
      cases hb : seg step' cut' K' x' with
      | cut y' =>
        rw [hb] at hs
        obtain ⟨j, _, le, runs⟩ := seg_cut_le hb
        obtain ⟨r', ran, r, ag, post⟩ := ih (rank y) (h ▸ lt) y rfl y' iy hs
        refine ⟨r', ?_, r, ag, post⟩
        have e1 := (runs ((rank y + 1) * K')).1
        rw [ran] at e1
        apply run_mono _ e1
        have : (rank y + 1) * K' + K' ≤ (m + 1) * K' := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K' (by omega)
        omega
      | done _ | stuck | fuel => rw [hb] at hs; exact hs.elim

/-- The same from related first configurations that need not be cut points, with every rank of
the invariant at most `B`: the target ends within `(B + 2) * K'` steps. -/
theorem ends_within_sim_start {step : Step σ R} {cut : σ → Bool} {step' : Step τ R'}
    {cut' : τ → Bool} {Ag : R → R' → Prop} {Rel : σ → τ → Prop} {Inv : σ → Prop}
    {Post : R → Prop} (rank : σ → Nat) (K K' B : Nat) (hB : ∀ y, Inv y → rank y ≤ B)
    {x₀ : σ} {x₀' : τ} (rel : Rel x₀ x₀')
    (start : SegEnds Inv Post (fun _ => True) (seg step cut K x₀))
    (segment : ∀ x, Inv x → SegEnds Inv Post (fun y => rank y < rank x) (seg step cut K x))
    (sim : BoundedSim step cut step' cut' Ag Rel K') :
    ∃ r', run step' ((B + 2) * K') x₀' = some r' ∧ ∃ r, Ag r r' ∧ Post r := by
  obtain ⟨k, hs⟩ := sim x₀ x₀' rel
  have hne : seg step cut K x₀ ≠ .fuel := fun e => by rw [e] at start; exact start
  have hne' : seg step cut k x₀ ≠ .fuel := fun e => by rw [e] at hs; exact hs
  rw [seg_eq_of_ne_fuel hne' hne] at hs
  have hK : K' ≤ (B + 2) * K' := Nat.le_mul_of_pos_left K' (by omega)
  cases ha : seg step cut K x₀ with
  | fuel | stuck => rw [ha] at start; exact start.elim
  | done a =>
    rw [ha] at start hs
    cases hb : seg step' cut' K' x₀' with
    | done b =>
      rw [hb] at hs
      obtain ⟨j, _, le, runs⟩ := seg_done_le hb
      refine ⟨b, ?_, a, hs, start⟩
      have := runs ((B + 2) * K' - j)
      rwa [show (B + 2) * K' - j + j = (B + 2) * K' by omega] at this
    | cut _ | stuck | fuel => rw [hb] at hs; exact hs.elim
  | cut y =>
    rw [ha] at start hs
    cases hb : seg step' cut' K' x₀' with
    | cut y' =>
      rw [hb] at hs
      obtain ⟨j, _, le, runs⟩ := seg_cut_le hb
      obtain ⟨r', ran, r, ag, post⟩ := ends_within_sim rank K K' segment sim y y' start.1 hs
      refine ⟨r', ?_, r, ag, post⟩
      have e1 := (runs ((rank y + 1) * K')).1
      rw [ran] at e1
      apply run_mono _ e1
      have : (rank y + 1) * K' + K' ≤ (B + 2) * K' := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right K' (by have := hB y start.1; omega)
      omega
    | done _ | stuck | fuel => rw [hb] at hs; exact hs.elim

/-- A bounded simulation from one obligation per pair of cut points, each target segment with its
own literal fuel at most `K'` (as the certify driver's `refine ⟨k, k', ?_⟩` gives): fuel beyond a
segment's end changes nothing (`seg_fuel_mono`). -/
theorem BoundedSim.of_each {step : Step σ R} {cut : σ → Bool} {step' : Step τ R'}
    {cut' : τ → Bool} {Ag : R → R' → Prop} {rels : List (σ → τ → Prop)} {K' : Nat}
    (each : ∀ P ∈ rels, ∀ x x', P x x' → ∃ k k', k' ≤ K' ∧
      SegRel Ag (fun y y' => ∃ Q ∈ rels, Q y y') (seg step cut k x) (seg step' cut' k' x')) :
    BoundedSim step cut step' cut' Ag (fun x x' => ∃ P ∈ rels, P x x') K' := by
  rintro x x' ⟨P, mem, holds⟩
  obtain ⟨k, k', le, h⟩ := each P mem x x' holds
  have ne : seg step' cut' k' x' ≠ .fuel := fun e => by
    rw [e] at h
    cases ha : seg step cut k x <;> rw [ha] at h <;> exact h
  exact ⟨k, by rw [seg_fuel_mono le ne]; exact h⟩

/-- Bounded simulations compose, segment for segment, with the last stage's bound. -/
theorem BoundedSim.trans {υ : Type u} {R'' : Type v} {step : Step σ R} {cut : σ → Bool}
    {step' : Step τ R'} {cut' : τ → Bool} {step'' : Step υ R''} {cut'' : υ → Bool}
    {Ag : R → R' → Prop} {Ag' : R' → R'' → Prop} {Rel : σ → τ → Prop} {Rel' : τ → υ → Prop}
    {K' K'' : Nat}
    (h : BoundedSim step cut step' cut' Ag Rel K') (h' : BoundedSim step' cut' step'' cut'' Ag' Rel' K'') :
    BoundedSim step cut step'' cut'' (fun a c => ∃ b, Ag a b ∧ Ag' b c)
      (fun x z => ∃ y, Rel x y ∧ Rel' y z) K'' := by
  rintro x z ⟨y, r1, r2⟩
  obtain ⟨k, s1⟩ := h x y r1
  obtain ⟨k', s2⟩ := h' y z r2
  have n1 : seg step' cut' K' y ≠ .fuel := fun e => by
    rw [e] at s1
    cases ha : seg step cut k x <;> rw [ha] at s1 <;> exact s1
  have n2 : seg step' cut' k' y ≠ .fuel := fun e => by rw [e] at s2; exact s2
  rw [seg_eq_of_ne_fuel n2 n1] at s2
  refine ⟨k, ?_⟩
  cases ha : seg step cut k x <;> cases hb : seg step' cut' K' y <;>
    cases hc : seg step'' cut'' K'' z <;>
    simp only [ha, hb, hc, SegRel] at s1 s2 ⊢
  all_goals first
    | exact ⟨_, s1, s2⟩
    | trivial
    | exact s1.elim
    | exact s2.elim

/-- info: 'SolarTV.CutPoint.ends_within_sim_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ends_within_sim_start

end Sim

/-! ## Resources -/

/-- How a metered run ends: in a result with the gas left, out of gas, or stuck. -/
inductive Metered (R : Type v) where
  | done (r : R) (left : Nat)
  | oog
  | stuck
  deriving DecidableEq

/-- A metered run: each step from `x` is charged `cost x` before it is taken, and the run fails
with `oog` when less gas is left, as the EVM charges an instruction before running it. The fuel
`n` only bounds the recursion; `none` when it runs out. -/
def runGas (step : Step σ R) (cost : σ → Nat) : Nat → Nat → σ → Option (Metered R)
  | 0, _, _ => none
  | n + 1, g, x =>
    if g < cost x then some .oog else
    match step x with
    | some (.inl r) => some (.done r (g - cost x))
    | some (.inr y) => runGas step cost n (g - cost x) y
    | none => some .stuck

/-- What a segment costs: the charge of each step it takes. -/
def segCost (step : Step σ R) (cut : σ → Bool) (cost : σ → Nat) : Nat → σ → Nat
  | 0, _ => 0
  | k + 1, x =>
    cost x + match step x with
      | some (.inr y) => if cut y then 0 else segCost step cut cost k y
      | _ => 0

section Metered

variable {step : Step σ R} {cut : σ → Bool} {cost : σ → Nat}

/-- **The resource bound is separate from the behaviour**: a metered run that ends gives the
result the unmetered run gives with the same fuel. -/
theorem runGas_done_run : ∀ {n g : Nat} {x : σ} {r : R} {left : Nat},
    runGas step cost n g x = some (.done r left) → run step n x = some r
  | 0, _, _, _, _, h => by cases h
  | n + 1, g, x, r, left, h => by
    simp only [runGas] at h
    split at h
    · cases h
    · simp only [run]
      cases e : step x with
      | none => rw [e] at h; cases h
      | some v =>
        cases v with
        | inl r' => rw [e] at h; cases h; rfl
        | inr y => rw [e] at h; exact runGas_done_run h

theorem segCost_cut : ∀ {k : Nat} {x y : σ} {g : Nat}, seg step cut k x = .cut y →
    segCost step cut cost k x ≤ g →
    ∃ j, j ≤ k ∧ ∀ n, runGas step cost (n + j) g x = runGas step cost n (g - segCost step cut cost k x) y
  | 0, _, _, _, h, _ => by cases h
  | k + 1, x, y, g, h, hg => by
    simp only [seg] at h
    simp only [segCost] at hg ⊢
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r => rw [e] at h; cases h
      | inr z =>
        simp only [e] at h hg ⊢
        by_cases c : cut z = true
        · simp only [c, ↓reduceIte] at h hg ⊢
          cases h
          refine ⟨1, by omega, fun n => ?_⟩
          simp only [runGas, show ¬ g < cost x by omega, ↓reduceIte, e, Nat.add_zero]
        · simp only [c, Bool.false_eq_true, ↓reduceIte] at h hg ⊢
          obtain ⟨j, le, runs⟩ := segCost_cut (g := g - cost x) h (by omega)
          refine ⟨j + 1, by omega, fun n => ?_⟩
          rw [← Nat.add_assoc]
          simp only [runGas, show ¬ g < cost x by omega, ↓reduceIte, e]
          rw [runs n, Nat.sub_sub]

theorem segCost_done : ∀ {k : Nat} {x : σ} {r : R} {g : Nat}, seg step cut k x = .done r →
    segCost step cut cost k x ≤ g →
    ∃ j, j ≤ k ∧ ∀ n, runGas step cost (n + j) g x = some (.done r (g - segCost step cut cost k x))
  | 0, _, _, _, h, _ => by cases h
  | k + 1, x, r, g, h, hg => by
    simp only [seg] at h
    simp only [segCost] at hg ⊢
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r' =>
        simp only [e] at h hg ⊢
        cases h
        refine ⟨1, by omega, fun n => ?_⟩
        simp only [runGas, show ¬ g < cost x by omega, ↓reduceIte, e, Nat.add_zero]
      | inr z =>
        simp only [e] at h hg ⊢
        by_cases c : cut z = true
        · simp only [c, ↓reduceIte] at h; cases h
        · simp only [c, Bool.false_eq_true, ↓reduceIte] at h hg ⊢
          obtain ⟨j, le, runs⟩ := segCost_done (g := g - cost x) h (by omega)
          refine ⟨j + 1, by omega, fun n => ?_⟩
          rw [← Nat.add_assoc]
          simp only [runGas, show ¬ g < cost x by omega, ↓reduceIte, e]
          rw [runs n, Nat.sub_sub]

/-- **Enough gas from the ranking**: when every segment of the certificate costs at most `C`,
a metered run from a cut point of rank `r` with at least `(r + 1) * C` gas never runs out of gas:
it ends, in a result meeting `Post`. -/
theorem gas_ends (rank : σ → Nat) (K C : Nat) {Inv : σ → Prop} {Post : R → Prop}
    (segment : ∀ x, Inv x → SegEnds Inv Post (fun y => rank y < rank x) (seg step cut K x) ∧
      segCost step cut cost K x ≤ C) :
    ∀ x, Inv x → ∀ g, (rank x + 1) * C ≤ g →
      ∃ n r left, runGas step cost n g x = some (.done r left) ∧ Post r := by
  intro x
  induction h : rank x using Nat.strongRecOn generalizing x with
  | ind m ih =>
    intro inv g hg
    obtain ⟨hk, hc⟩ := segment x inv
    have hCg : C ≤ g := Nat.le_trans (Nat.le_mul_of_pos_left C (Nat.succ_pos m)) hg
    cases hs : seg step cut K x with
    | fuel | stuck => rw [hs] at hk; exact hk.elim
    | done a =>
      rw [hs] at hk
      obtain ⟨j, _, runs⟩ := segCost_done (cost := cost) (g := g) hs (by omega)
      exact ⟨0 + j, a, _, runs 0, hk⟩
    | cut y =>
      rw [hs] at hk
      obtain ⟨iy, lt⟩ := hk
      obtain ⟨j, _, runs⟩ := segCost_cut (cost := cost) (g := g) hs (by omega)
      have hg' : (rank y + 1) * C ≤ g - segCost step cut cost K x := by
        have : (rank y + 1) * C + C ≤ (m + 1) * C := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right C (by omega)
        omega
      obtain ⟨n, r, left, ran, post⟩ := ih (rank y) (h ▸ lt) y rfl iy _ hg'
      exact ⟨n + j, r, left, by rw [runs n]; exact ran, post⟩

/-- Each step charged one unit: the segment's cost is at most its fuel. -/
theorem segCost_one_le : ∀ (k : Nat) (x : σ), segCost step cut (fun _ => 1) k x ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, x => by
    simp only [segCost]
    split
    · split
      · omega
      · have := segCost_one_le k ‹_›; omega
    · omega

end Metered

/-! ## Controls -/

namespace Negative

/-- A loop on `i` up to `5`, every configuration a cut point. `good` adds one per iteration;
`flat` forgets to. -/
def good : Step Nat Nat := fun i => if i < 5 then some (.inr (i + 1)) else some (.inl i)
def flat : Step Nat Nat := fun i => if i < 5 then some (.inr i) else some (.inl i)
def everywhere : Nat → Bool := fun _ => true
def rank : Nat → Nat := fun i => 5 - i

/-- The certificate `(i ≤ 5, 5 - i)` checks for the good loop, by evaluation. -/
theorem good_accepted : ∀ i, i ≤ 5 →
    SegEnds (fun i => i ≤ 5) (fun r => r = 5) (fun y => rank y < rank i) (seg good everywhere 1 i) := by
  intro i hi
  by_cases h : i < 5
  · simp only [seg, good, everywhere, rank, SegEnds, h, ↓reduceIte]; omega
  · simp only [seg, good, SegEnds, h, ↓reduceIte]; omega

theorem good_ends : ∃ r, run good ((5 + 2) * 1) 0 = some r ∧ r = 5 :=
  ends_within_start rank 1 5 (fun _ h => by simp only [rank]; omega)
    (by decide) good_accepted

/-- **A ranking certificate that does not fall is rejected**: for the loop that forgets its
increment, the same certificate's obligation at `i = 3` is false, and `decide` evaluates it to
`False` (a mismatch, at once). -/
theorem flat_rejected :
    ¬ SegEnds (fun i => i ≤ 5) (fun r => r = 5) (fun y => rank y < rank 3) (seg flat everywhere 1 3) := by
  decide

/-- No fuel helps: at every fuel, the flat loop's segment from `3` is not one the certificate
accepts, so no certificate with this rank checks. -/
theorem flat_rejected_all (k : Nat) :
    ¬ SegEnds (fun i => i ≤ 5) (fun r => r = 5) (fun y => rank y < rank 3) (seg flat everywhere k 3) := by
  cases k with
  | zero => simp [seg, SegEnds]
  | succ k => simp [seg, flat, everywhere, SegEnds, rank]

/-- **The gas bound is not vacuous**: the good loop costs `6` steps from `0`; with `5` gas it
runs out of gas, with `6` it ends. -/
theorem oog_below : runGas good (fun _ => 1) 10 5 0 = some .oog := by decide
theorem ends_at_bound : ∃ left, runGas good (fun _ => 1) 10 6 0 = some (.done 5 left) := ⟨0, by decide⟩

end Negative

/-- info: 'SolarTV.CutPoint.gas_ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms gas_ends

/-- info: 'SolarTV.CutPoint.ends_within_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ends_within_start

end SolarTV.CutPoint
