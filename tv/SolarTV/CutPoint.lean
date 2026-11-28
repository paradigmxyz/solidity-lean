import SolarTV.Machine

/-! Whole runs from loop-free segments between cut points.

A stage whose programs loop cannot be proved by running both on a call to their ends, as the
loop-free stages are: a loop runs as many times as its data says. Instead, each program gets
cut points, configurations such as the headers of its loops, so that every cycle of its control
flow passes through one, and the two programs get a relation between their configurations at
cut points. A segment runs a program from a configuration for at least one step and on until it
reaches a cut point, ends, or is stuck (\`seg\`); it is loop-free, so symbolic execution runs it
to the end with fuel the number of blocks (\`seg_ne_fuel\` shows such fuel suffices when every
cycle passes through a cut point). \`Sim\` asks that from every related pair of configurations,
both segments end alike: in results that agree, at cut points that are related again, or both
stuck. Running out of a segment's fuel matches nothing, so a segment that does not end where the
procedure expects fails the proof, by mismatch.

From that alone, whole runs are related for any number of loop iterations (\`Sim.ends\`,
\`Sim.ends_back\`): every end of one program at some fuel is matched by an agreeing end of the
other at some fuel, in both directions, so one program ends exactly when the other does
(\`Sim.ends_iff\`); one is stuck exactly when the other is (\`Sim.stuck_iff\`); and one runs forever
exactly when the other does (\`Sim.diverges_iff\`). None of these holds vacuously: the segment
obligation has no case for running out of fuel, and each segment takes at least one step, so
an infinite run of one program is matched step for step by an infinite run of the other.

Nothing here depends on what a configuration is, so the same theorem serves every stage whose
programs run as a step function with fuel (\`Machine.iterate\`): MIR to MIR, MIR to EVM IR and EVM
IR to EVM IR, and EVM IR to any bytecode semantics given as a step function. The relation is the
exporter's: it derives it from what the compiler records at each cut point (the values that
correspond, the phis, the stack layout of a loop header); this file proves no invariant of its
own. \`certified\` and \`certified_back\` state the result for layers. -/

namespace SolarTV.CutPoint

universe u v u' v'

/-- A machine of configurations \`σ\` and results \`R\`: one step ends in a result, continues from
a new configuration, or is stuck (\`none\`). -/
abbrev Step (σ : Type u) (R : Type v) := σ → Option (R ⊕ σ)

variable {σ : Type u} {R : Type v} {τ : Type u'} {R' : Type v'}

/-- A run with fuel, one unit per step, as \`Machine.iterate\` runs: the result, or \`none\` when the
fuel runs out or the machine is stuck. -/
def run (step : Step σ R) : Nat → σ → Option R
  | 0, _ => none
  | n + 1, x =>
    match step x with
    | some (.inl r) => some r
    | some (.inr y) => run step n y
    | none => none

/-- \`k\` steps from a configuration: the result reached on the way, the configuration after
them, or \`none\` when the machine is stuck on the way. -/
def steps (step : Step σ R) : Nat → σ → Option (R ⊕ σ)
  | 0, x => some (.inr x)
  | k + 1, x =>
    match step x with
    | some (.inl r) => some (.inl r)
    | some (.inr y) => steps step k y
    | none => none

/-- A configuration from which the machine runs forever. -/
def Diverges (step : Step σ R) (x : σ) : Prop := ∀ k, ∃ y, steps step k x = some (.inr y)

/-- A configuration from which the machine gets stuck. -/
def Stuck (step : Step σ R) (x : σ) : Prop := ∃ k, steps step k x = none

/-- How a segment ends: in a result, at a cut point, stuck, or out of its fuel. -/
inductive Seg (R : Type v) (σ : Type u) where
  | done (r : R)
  | cut (y : σ)
  | stuck
  | fuel

/-- A segment from \`x\`: one step, then on until a cut point, an end or a stuck step, for at most
\`k\` steps in all. -/
def seg (step : Step σ R) (cut : σ → Bool) : Nat → σ → Seg R σ
  | 0, _ => .fuel
  | k + 1, x =>
    match step x with
    | none => .stuck
    | some (.inl r) => .done r
    | some (.inr y) => if cut y then .cut y else seg step cut k y

/-- Two segments that end alike: in agreeing results, at related cut points, or both stuck.
Running out of fuel matches nothing. -/
def SegRel (Ag : R → R' → Prop) (Rel : σ → τ → Prop) : Seg R σ → Seg R' τ → Prop
  | .done r, .done r' => Ag r r'
  | .cut y, .cut y' => Rel y y'
  | .stuck, .stuck => True
  | _, _ => False

theorem SegRel.flip {Ag : R → R' → Prop} {Rel : σ → τ → Prop} :
    ∀ {a : Seg R σ} {b : Seg R' τ}, SegRel Ag Rel a b →
      SegRel (fun r' r => Ag r r') (fun y' y => Rel y y') b a
  | .done _, .done _, h | .cut _, .cut _, h | .stuck, .stuck, h => h
  | .done _, .cut _, h | .done _, .stuck, h | .done _, .fuel, h
  | .cut _, .done _, h | .cut _, .stuck, h | .cut _, .fuel, h
  | .stuck, .done _, h | .stuck, .cut _, h | .stuck, .fuel, h
  | .fuel, _, h => h.elim

/-! Runs and steps. -/

section Runs

variable {step : Step σ R}

theorem run_eq_steps : ∀ (n : Nat) (x : σ),
    run step n x = match steps step n x with | some (.inl r) => some r | _ => none
  | 0, _ => rfl
  | n + 1, x => by
    simp only [run, steps]
    cases step x with
    | none => rfl
    | some v =>
      cases v with
      | inl r => rfl
      | inr y => exact run_eq_steps n y

theorem run_of_steps {n : Nat} {x : σ} {r : R} (h : steps step n x = some (.inl r)) :
    run step n x = some r := by
  rw [run_eq_steps, h]

theorem steps_of_run {n : Nat} {x : σ} {r : R} (h : run step n x = some r) :
    steps step n x = some (.inl r) := by
  rw [run_eq_steps] at h
  split at h
  · rename_i e; cases h; exact e
  · cases h

/-- Past an end or a stuck step, more steps change nothing. -/
theorem steps_succ : ∀ {k : Nat} {x : σ}, (∀ y, steps step k x ≠ some (.inr y)) →
    steps step (k + 1) x = steps step k x
  | 0, x, h => absurd rfl (h x)
  | k + 1, x, h => by
    simp only [steps] at h ⊢
    cases e : step x with
    | none => rfl
    | some v =>
      cases v with
      | inl r => rfl
      | inr y =>
        rw [e] at h
        exact steps_succ h

theorem steps_le {k k' : Nat} {x : σ} (le : k ≤ k') (h : ∀ y, steps step k x ≠ some (.inr y)) :
    steps step k' x = steps step k x := by
  induction le with
  | refl => rfl
  | step _ ih =>
    rw [steps_succ (by rw [ih]; exact h), ih]

theorem run_mono {n m : Nat} {x : σ} {r : R} (le : n ≤ m) (h : run step n x = some r) :
    run step m x = some r := by
  apply run_of_steps
  rw [steps_le le (by rw [steps_of_run h]; intro y e; cases e)]
  exact steps_of_run h

/-- A run ends in at most one result, whatever its fuel. -/
theorem run_unique {n m : Nat} {x : σ} {a b : R} (ha : run step n x = some a)
    (hb : run step m x = some b) : a = b := by
  have := run_mono (Nat.le_max_left n m) ha
  rw [run_mono (Nat.le_max_right n m) hb] at this
  exact (Option.some.inj this).symm

theorem not_stuck_of_diverges {x : σ} (d : Diverges step x) : ¬Stuck step x := by
  intro ⟨k, h⟩
  obtain ⟨y, e⟩ := d k
  rw [h] at e
  cases e

theorem not_run_of_diverges {x : σ} (d : Diverges step x) (n : Nat) (r : R) :
    run step n x ≠ some r := by
  intro h
  obtain ⟨y, e⟩ := d n
  rw [steps_of_run h] at e
  cases e

/-- A run that neither ends nor gets stuck runs forever. -/
theorem diverges_of {x : σ} (noEnd : ∀ n r, run step n x ≠ some r) (noStuck : ¬Stuck step x) :
    Diverges step x := by
  intro k
  cases e : steps step k x with
  | none => exact absurd ⟨k, e⟩ noStuck
  | some v =>
    cases v with
    | inl r => exact absurd (run_of_steps e) (noEnd k r)
    | inr y => exact ⟨y, rfl⟩

theorem iterate_eq {ς : Type} (step : Step ς (Machine.Halt × Machine.State)) :
    ∀ (n : Nat) (x : ς), Machine.iterate step n x = run step n x
  | 0, _ => rfl
  | n + 1, x => by
    simp only [Machine.iterate, run]
    cases step x with
    | none => rfl
    | some v =>
      cases v with
      | inl r => rfl
      | inr y => exact iterate_eq step n y

/-- Two counts of steps that both stop (in a result or a stuck step) stop alike. -/
private theorem steps_stop {k j : Nat} {x : σ} (hk : ∀ y, steps step k x ≠ some (.inr y))
    (hj : ∀ y, steps step j x ≠ some (.inr y)) : steps step k x = steps step j x := by
  rw [← steps_le (Nat.le_max_left k j) hk, ← steps_le (Nat.le_max_right k j) hj]

/-- After `j` steps to a configuration, the run goes on from it. -/
private theorem steps_after : ∀ {j : Nat} {x y : σ}, steps step j x = some (.inr y) →
    ∀ n, steps step (n + j) x = steps step n y
  | 0, _, _, h, _ => by cases h; rfl
  | j + 1, x, y, h, n => by
    simp only [steps] at h ⊢
    cases e : step x with
    | none => rw [e] at h; cases h
    | some v =>
      cases v with
      | inl r => rw [e] at h; cases h
      | inr z => rw [e] at h; exact steps_after h n

end Runs

/-! What a segment says about whole runs. -/

section Segments

variable {step : Step σ R} {cut : σ → Bool}

/-- A segment that stops, short of its fuel, took `j` steps, `1 ≤ j ≤ k`, to where it stopped:
its result, its cut point or a stuck step. -/
private theorem seg_steps : ∀ {k : Nat} {x : σ}, seg step cut k x ≠ .fuel →
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ steps step j x = match seg step cut k x with
      | .done r => some (.inl r)
      | .cut y => some (.inr y)
      | _ => none
  | 0, _, h => absurd rfl h
  | k + 1, x, h => by
    simp only [seg] at h ⊢
    cases e : step x with
    | none => exact ⟨1, Nat.le_refl 1, by omega, by simp only [steps, e]⟩
    | some v =>
      cases v with
      | inl r => exact ⟨1, Nat.le_refl 1, by omega, by simp only [steps, e]⟩
      | inr z =>
        rw [e] at h
        by_cases c : cut z = true
        · simp only [c, ↓reduceIte]
          exact ⟨1, Nat.le_refl 1, by omega, by simp only [steps, e]⟩
        · simp only [c, Bool.false_eq_true, ↓reduceIte] at h ⊢
          obtain ⟨j, pos, le, hj⟩ := seg_steps h
          exact ⟨j + 1, by omega, by omega, by simp only [steps, e]; exact hj⟩

/-- A segment that reaches a cut point ran \`j ≥ 1\` steps to it. -/
theorem seg_cut : ∀ {k : Nat} {x y : σ}, seg step cut k x = .cut y →
    ∃ j, 1 ≤ j ∧ ∀ n, run step (n + j) x = run step n y ∧ steps step (n + j) x = steps step n y := by
  intro k x y h
  obtain ⟨j, pos, -, hj⟩ := seg_steps (by rw [h]; nofun)
  rw [h] at hj
  exact ⟨j, pos, fun n => ⟨by rw [run_eq_steps, run_eq_steps, steps_after hj], steps_after hj n⟩⟩

/-- A segment that ends ran \`j ≥ 1\` steps to its result. -/
theorem seg_done : ∀ {k : Nat} {x : σ} {r : R}, seg step cut k x = .done r →
    ∃ j, 1 ≤ j ∧ ∀ n, run step (n + j) x = some r := by
  intro k x r h
  obtain ⟨j, pos, -, hj⟩ := seg_steps (by rw [h]; nofun)
  rw [h] at hj
  exact ⟨j, pos, fun n => run_mono (Nat.le_add_left j n) (run_of_steps hj)⟩

/-- A segment that gets stuck never ends, and is stuck after \`j\` steps. -/
theorem seg_stuck : ∀ {k : Nat} {x : σ}, seg step cut k x = .stuck →
    (∀ n, run step n x = none) ∧ ∃ j, steps step j x = none := by
  intro k x h
  obtain ⟨j, -, -, hj⟩ := seg_steps (by rw [h]; nofun)
  rw [h] at hj
  refine ⟨fun n => ?_, j, hj⟩
  cases ran : run step n x with
  | none => rfl
  | some r =>
    have := steps_stop (j := j) (by rw [steps_of_run ran]; nofun) (by rw [hj]; nofun)
    rw [steps_of_run ran, hj] at this
    cases this

/-- Cut points that cover every cycle bound every segment: when every step to a configuration
that is no cut point climbs a rank bounded by \`N\` (a topological order of the control flow with
the edges into cut points removed, which is acyclic exactly when every cycle passes through a cut
point), a segment with more than \`N\` steps of fuel never runs out of it. -/
theorem seg_ne_fuel (rank : σ → Nat) (N : Nat) (bound : ∀ x, rank x ≤ N)
    (climbs : ∀ x y, step x = some (.inr y) → cut y = false → rank x < rank y) :
    ∀ (k : Nat) (x : σ), N - rank x < k → seg step cut k x ≠ .fuel
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, x, h => by
    simp only [seg]
    cases e : step x with
    | none => simp
    | some v =>
      cases v with
      | inl r => simp
      | inr y =>
        simp only
        cases c : cut y with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have := climbs x y e c
          have := bound y
          exact seg_ne_fuel rank N bound climbs k y (by omega)

end Segments

/-! The simulation. -/

/-- From every pair of related configurations, the two segments end alike. This is what symbolic
execution proves, segment by segment, at each pair of cut points; the relation holds of the two
programs' first configurations too, which need not be cut points. -/
structure Sim (step : Step σ R) (cut : σ → Bool) (step' : Step τ R') (cut' : τ → Bool)
    (Ag : R → R' → Prop) (Rel : σ → τ → Prop) : Prop where
  segment : ∀ x x', Rel x x' → ∃ k k', SegRel Ag Rel (seg step cut k x) (seg step' cut' k' x')

namespace Sim

variable {step : Step σ R} {cut : σ → Bool} {step' : Step τ R'} {cut' : τ → Bool}
  {Ag : R → R' → Prop} {Rel : σ → τ → Prop}

/-- The simulation read backwards. -/
theorem flip (S : Sim step cut step' cut' Ag Rel) :
    Sim step' cut' step cut (fun r' r => Ag r r') (fun y' y => Rel y y') where
  segment x' x rel := by
    obtain ⟨k, k', h⟩ := S.segment x x' rel
    exact ⟨k', k, h.flip⟩

/-- Every run of the first program that stops, `steps step k x = t.map .inl` in a result
(`t = some r`) or a stuck step (`t = none`), is matched by a run of the second that stops alike,
in an agreeing result or a stuck step. -/
private theorem final (S : Sim step cut step' cut' Ag Rel) :
    ∀ (k : Nat) (x : σ) (x' : τ) (t : Option R), Rel x x' → steps step k x = t.map .inl →
      ∃ m t', steps step' m x' = t'.map .inl ∧ Option.Rel Ag t t' := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro x x' t rel stop
    have stops : ∀ y, steps step k x ≠ some (.inr y) := by rw [stop]; cases t <;> nofun
    obtain ⟨k₁, k₁', h⟩ := S.segment x x' rel
    have ne : seg step cut k₁ x ≠ .fuel := fun e => by rw [e] at h; exact h
    have ne' : seg step' cut' k₁' x' ≠ .fuel := fun e => by
      rw [e] at h; revert h; cases seg step cut k₁ x <;> exact id
    obtain ⟨j, pos, -, hj⟩ := seg_steps ne
    obtain ⟨j', -, -, hj'⟩ := seg_steps ne'
    cases hs : seg step cut k₁ x <;> cases hs' : seg step' cut' k₁' x' <;>
      simp only [hs, hs', SegRel] at h hj hj'
    case done.done a a' =>
      rw [steps_stop stops (by rw [hj]; nofun), hj] at stop
      cases t <;> cases stop
      exact ⟨j', some a', hj', .some h⟩
    case stuck.stuck =>
      rw [steps_stop stops (by rw [hj]; nofun), hj] at stop
      cases t <;> cases stop
      exact ⟨j', none, hj', .none⟩
    case cut.cut y y' =>
      by_cases le : j ≤ k
      · rw [show k = (k - j) + j by omega, steps_after hj] at stop
        obtain ⟨m, t', hm, ht⟩ := ih (k - j) (by omega) y y' t h stop
        exact ⟨m + j', t', by rw [steps_after hj']; exact hm, ht⟩
      · -- Stopped before the cut point, which the run reaches: impossible.
        have := steps_le (Nat.le_of_lt (Nat.lt_of_not_le le)) stops
        rw [hj, stop] at this
        cases t <;> cases this

/-- Every end of the first program, at any fuel, is matched by an agreeing end of the second. -/
theorem ends (S : Sim step cut step' cut' Ag Rel) :
    ∀ (n : Nat) (x : σ) (x' : τ) (r : R), Rel x x' → run step n x = some r →
      ∃ m r', run step' m x' = some r' ∧ Ag r r' := by
  intro n x x' r rel ran
  obtain ⟨m, _, hm, ⟨ag⟩⟩ := S.final n x x' (some r) rel (steps_of_run ran)
  exact ⟨m, _, run_of_steps hm, ag⟩

/-- Every end of the second program is matched by an agreeing end of the first. -/
theorem ends_back (S : Sim step cut step' cut' Ag Rel) (m : Nat) (x : σ) (x' : τ) (r' : R')
    (rel : Rel x x') (ran : run step' m x' = some r') :
    ∃ n r, run step n x = some r ∧ Ag r r' :=
  S.flip.ends m x' x r' rel ran

/-- One program ends at some fuel exactly when the other does. -/
theorem ends_iff (S : Sim step cut step' cut' Ag Rel) {x : σ} {x' : τ} (rel : Rel x x') :
    (∃ n r, run step n x = some r) ↔ (∃ m r', run step' m x' = some r') := by
  constructor
  · intro ⟨n, r, ran⟩
    obtain ⟨m, r', ran', _⟩ := S.ends n x x' r rel ran
    exact ⟨m, r', ran'⟩
  · intro ⟨m, r', ran'⟩
    obtain ⟨n, r, ran, _⟩ := S.ends_back m x x' r' rel ran'
    exact ⟨n, r, ran⟩

/-- A stuck first program has a stuck second program. -/
theorem stuck (S : Sim step cut step' cut' Ag Rel) :
    ∀ (k : Nat) (x : σ) (x' : τ), Rel x x' → steps step k x = none → Stuck step' x' := by
  intro k x x' rel stuckAt
  obtain ⟨m, _, hm, ⟨⟩⟩ := S.final k x x' none rel stuckAt
  exact ⟨m, hm⟩

theorem stuck_iff (S : Sim step cut step' cut' Ag Rel) {x : σ} {x' : τ} (rel : Rel x x') :
    Stuck step x ↔ Stuck step' x' :=
  ⟨fun ⟨k, h⟩ => S.stuck k x x' rel h, fun ⟨k, h⟩ => S.flip.stuck k x' x rel h⟩

/-- One program runs forever exactly when the other does: an infinite run is matched by an
infinite run, never by an end or a stuck step. -/
theorem diverges_iff (S : Sim step cut step' cut' Ag Rel) {x : σ} {x' : τ} (rel : Rel x x') :
    Diverges step x ↔ Diverges step' x' := by
  constructor
  · intro d
    apply diverges_of
    · intro m r' ran'
      obtain ⟨n, r, ran, _⟩ := S.ends_back m x x' r' rel ran'
      exact not_run_of_diverges d n r ran
    · intro st
      exact not_stuck_of_diverges d ((S.stuck_iff rel).2 st)
  · intro d
    apply diverges_of
    · intro n r ran
      obtain ⟨m, r', ran', _⟩ := S.ends n x x' r rel ran
      exact not_run_of_diverges d m r' ran'
    · intro st
      exact not_stuck_of_diverges d ((S.stuck_iff rel).1 st)

/-- A simulation from one obligation per pair of cut points: the relation is that one of the
pairs' relations holds, and each segment from a pair ends at a pair. -/
theorem of_each {rels : List (σ → τ → Prop)}
    (each : ∀ P ∈ rels, ∀ x x', P x x' → ∃ k k',
      SegRel Ag (fun y y' => ∃ Q ∈ rels, Q y y') (seg step cut k x) (seg step' cut' k' x')) :
    Sim step cut step' cut' Ag (fun x x' => ∃ P ∈ rels, P x x') where
  segment x x' := fun ⟨P, mem, holds⟩ => each P mem x x' holds

end Sim

/-! Layers. -/

open Machine

theorem Agree.symm {a b : Halt × State} (h : Agree a b) : Agree b a := by
  obtain ⟨ha, sa⟩ := a
  obtain ⟨hb, sb⟩ := b
  cases ha <;> cases hb <;> simp_all [Agree] <;> (try exact h.symm) <;> (try omega)
  all_goals (obtain ⟨k, st, tr, w⟩ := h; exact ⟨k.symm, st.symm, tr.symm, w.symm⟩)

/-- Two programs of layers that run as step functions from each call's first configuration,
simulated through cut points on every call in scope. -/
structure LayerSim (A B : Layer) (o : Oracle) (p : A.Prog) (q : B.Prog) (scope : Call → Prop)
    where
  σ : Type
  τ : Type
  step : Call → Step σ (Halt × State)
  step' : Call → Step τ (Halt × State)
  init : Call → σ
  init' : Call → τ
  runs : ∀ call n, A.run o p call n = Machine.iterate (step call) n (init call)
  runs' : ∀ call n, B.run o q call n = Machine.iterate (step' call) n (init' call)
  cut : σ → Bool
  cut' : τ → Bool
  Rel : Call → σ → τ → Prop
  start : ∀ call, scope call → Rel call (init call) (init' call)
  sim : ∀ call, scope call → Sim (step call) cut (step' call) cut' Agree (Rel call)

namespace LayerSim

variable {A B : Layer} {o : Oracle} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}

/-- Every end of \`p\` is matched by an agreeing end of \`q\`: a stage. -/
theorem certified (S : LayerSim A B o p q scope) : Certified A B o p q scope := by
  intro call inScope r ⟨n, ran⟩
  rw [S.runs, iterate_eq] at ran
  obtain ⟨m, r', ran', ag⟩ := (S.sim call inScope).ends n _ _ r (S.start call inScope) ran
  exact ⟨r', ⟨m, by rw [S.runs', iterate_eq]; exact ran'⟩, ag⟩

/-- Every end of \`q\` is matched by an agreeing end of \`p\`: the stage backwards, so \`q\` ends on a
call exactly when \`p\` does, and diverges exactly when \`p\` does. -/
theorem certified_back (S : LayerSim A B o p q scope) : Certified B A o q p scope := by
  intro call inScope r' ⟨m, ran'⟩
  rw [S.runs', iterate_eq] at ran'
  obtain ⟨n, r, ran, ag⟩ :=
    (S.sim call inScope).ends_back m _ _ r' (S.start call inScope) ran'
  exact ⟨r, ⟨n, by rw [S.runs, iterate_eq]; exact ran⟩, Agree.symm ag⟩

theorem ends_iff (S : LayerSim A B o p q scope) (call : Call) (inScope : scope call) :
    (∃ r, A.Ends o p call r) ↔ (∃ r', B.Ends o q call r') := by
  constructor
  · intro ⟨r, e⟩
    obtain ⟨r', e', _⟩ := S.certified call inScope r e
    exact ⟨r', e'⟩
  · intro ⟨r', e'⟩
    obtain ⟨r, e, _⟩ := S.certified_back call inScope r' e'
    exact ⟨r, e⟩

theorem diverges_iff (S : LayerSim A B o p q scope) (call : Call) (inScope : scope call) :
    Diverges (S.step call) (S.init call) ↔ Diverges (S.step' call) (S.init' call) :=
  (S.sim call inScope).diverges_iff (S.start call inScope)

theorem stuck_iff (S : LayerSim A B o p q scope) (call : Call) (inScope : scope call) :
    Stuck (S.step call) (S.init call) ↔ Stuck (S.step' call) (S.init' call) :=
  (S.sim call inScope).stuck_iff (S.start call inScope)

end LayerSim

end SolarTV.CutPoint
