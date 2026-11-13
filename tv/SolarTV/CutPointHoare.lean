import SolarTV.CutPoint

/-! # Partial correctness through cut points

`SolarTV.CutPoint.Sim` relates two machines segment by segment. This is its one-machine
counterpart: an invariant `Inv` on cut-point configurations and a postcondition `Post` on
results. When every segment from a configuration meeting `Inv` (and from the first
configuration) ends in a result meeting `Post`, at a cut point meeting `Inv`, or stuck, every
result the machine reaches, at any fuel, meets `Post`, whatever number of times its loops run.
Running out of a segment's fuel proves nothing (`SegOk` of `.fuel` is `False`), so a proof
that leaves a segment unfinished fails. -/

namespace SolarTV.CutPoint

universe u v

variable {σ : Type u} {R : Type v}

/-- A segment that ends as the invariant and the postcondition ask: in a result meeting `Post`,
at a cut point meeting `Inv`, or stuck. -/
def SegOk (Inv : σ → Prop) (Post : R → Prop) : Seg R σ → Prop
  | .done r => Post r
  | .cut y => Inv y
  | .stuck => True
  | .fuel => False

/-- A weaker invariant at the cut points. -/
theorem SegOk.mono {Inv Inv' : σ → Prop} {Post : R → Prop} (h : ∀ y, Inv y → Inv' y) :
    ∀ {s : Seg R σ}, SegOk Inv Post s → SegOk Inv' Post s
  | .done _, p | .stuck, p => p
  | .cut y, p => h y p
  | .fuel, p => p.elim

/-- **Partial correctness through cut points.** If every segment from a configuration meeting
`Inv` ends as `SegOk` asks, every result of a run from such a configuration meets `Post`. -/
theorem post_of_segments {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    (segment : ∀ x, Inv x → ∃ k, SegOk Inv Post (seg step cut k x)) :
    ∀ (n : Nat) (x : σ) (r : R), Inv x → run step n x = some r → Post r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x r inv ran
    obtain ⟨k, h⟩ := segment x inv
    cases hs : seg step cut k x with
    | fuel => rw [hs] at h; exact h.elim
    | stuck =>
      rw [(seg_stuck hs).1 n] at ran
      cases ran
    | done a =>
      rw [hs] at h
      obtain ⟨j, _, runs⟩ := seg_done hs
      have e : r = a := run_unique ran (runs 0)
      subst e
      exact h
    | cut y =>
      rw [hs] at h
      obtain ⟨j, pos, runs⟩ := seg_cut hs
      by_cases le : j ≤ n
      · have e : n = (n - j) + j := by omega
        rw [e, (runs (n - j)).1] at ran
        exact ih (n - j) (by omega) y r h ran
      · have := run_mono (Nat.le_of_lt (Nat.lt_of_not_le le)) ran
        rw [show j = 0 + j from (Nat.zero_add j).symm, (runs 0).1] at this
        cases this

/-- The same from a first configuration that need not be a cut point: its segment ends as
`SegOk` asks too. -/
theorem post_of_start {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    {x₀ : σ} (start : ∃ k, SegOk Inv Post (seg step cut k x₀))
    (segment : ∀ x, Inv x → ∃ k, SegOk Inv Post (seg step cut k x)) :
    ∀ (n : Nat) (r : R), run step n x₀ = some r → Post r :=
  fun n r ran =>
    post_of_segments (step := step) (cut := cut) (Inv := fun x => x = x₀ ∨ Inv x)
      (fun x h => by
        rcases h with rfl | h
        · obtain ⟨k, hk⟩ := start
          exact ⟨k, SegOk.mono (fun _ h => Or.inr h) hk⟩
        · obtain ⟨k, hk⟩ := segment x h
          exact ⟨k, SegOk.mono (fun _ h => Or.inr h) hk⟩)
      n x₀ r (Or.inl rfl) ran

/-- info: 'SolarTV.CutPoint.post_of_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms post_of_start

/-! ## Total correctness

With a rank that every segment from a cut point lowers on its way to the next one, and no
segment stuck, every run from a configuration meeting the invariant ends, in a result meeting the
postcondition. -/

/-- A segment that ends, as the invariant and the postcondition ask, in a result meeting `Post`
or at a cut point meeting `Inv` and `below` (the rank fell): not stuck, nor out of fuel. -/
def SegEnds (Inv : σ → Prop) (Post : R → Prop) (below : σ → Prop) : Seg R σ → Prop
  | .done r => Post r
  | .cut y => Inv y ∧ below y
  | .stuck => False
  | .fuel => False

/-- **Total correctness through cut points.** -/
theorem ends_of_segments {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    (rank : σ → Nat)
    (segment : ∀ x, Inv x → ∃ k, SegEnds Inv Post (fun y => rank y < rank x) (seg step cut k x)) :
    ∀ x, Inv x → ∃ n r, run step n x = some r ∧ Post r := by
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
      exact ⟨0 + j, a, runs 0, hk⟩
    | cut y =>
      rw [hs] at hk
      obtain ⟨iy, lt⟩ := hk
      obtain ⟨j, _, runs⟩ := seg_cut hs
      obtain ⟨n, r, ran, post⟩ := ih (rank y) (h ▸ lt) y rfl iy
      exact ⟨n + j, r, by rw [(runs n).1]; exact ran, post⟩

/-- The same from a first configuration that need not be a cut point. -/
theorem ends_of_start {step : Step σ R} {cut : σ → Bool} {Inv : σ → Prop} {Post : R → Prop}
    (rank : σ → Nat) {x₀ : σ} (start : ∃ k, SegEnds Inv Post (fun _ => True) (seg step cut k x₀))
    (segment : ∀ x, Inv x → ∃ k, SegEnds Inv Post (fun y => rank y < rank x) (seg step cut k x)) :
    ∃ n r, run step n x₀ = some r ∧ Post r := by
  obtain ⟨k, hk⟩ := start
  cases hs : seg step cut k x₀ with
  | fuel | stuck => rw [hs] at hk; exact hk.elim
  | done a =>
    rw [hs] at hk
    obtain ⟨j, _, runs⟩ := seg_done hs
    exact ⟨0 + j, a, runs 0, hk⟩
  | cut y =>
    rw [hs] at hk
    obtain ⟨j, _, runs⟩ := seg_cut hs
    obtain ⟨n, r, ran, post⟩ := ends_of_segments rank segment y hk.1
    exact ⟨n + j, r, by rw [(runs n).1]; exact ran, post⟩

/-- info: 'SolarTV.CutPoint.ends_of_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ends_of_start

end SolarTV.CutPoint
