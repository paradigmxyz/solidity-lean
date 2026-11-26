import SolarTV.Termination

/-! A layer simulation through cut points, from a bounded simulation.

The certify driver proves each pass by symbolic execution of loop-free segments (`sym_seg`):
one obligation per relation of a list the exporter derives from what the compiler kept across the
pass, from related configurations to segments that end alike, the target's within a literal bound
(a `BoundedSim`, as `ends_within_sim_start` takes it). The rest is the same for every pass and
is here: a bounded simulation is a simulation (`BoundedSim.toSim`), and with the list's first
relation relating the two first configurations, the two layers' programs are simulated on every
call in scope (`LayerSim.ofRels`), so a stage both ways. -/

namespace SolarTV.CutPoint

open Machine

/-- A bounded simulation is a simulation, with the bound as the target's fuel. -/
theorem BoundedSim.toSim {σ : Type u} {R : Type v} {τ : Type u'} {R' : Type v'}
    {step : Step σ R} {cut : σ → Bool} {step' : Step τ R'} {cut' : τ → Bool}
    {Ag : R → R' → Prop} {Rel : σ → τ → Prop} {K' : Nat}
    (h : BoundedSim step cut step' cut' Ag Rel K') : Sim step cut step' cut' Ag Rel where
  segment x x' rel := match h x x' rel with | ⟨k, s⟩ => ⟨k, K', s⟩

/-- Two layers' programs simulated through cut points on every call in scope, from a list of
relations per call: one of them relates the two first configurations, and from every pair one of
them relates, the two segments end alike, the target's within `K'` steps, at pairs one of them
relates. -/
def LayerSim.ofRels {A B : Layer} {o : Oracle} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    {σ τ : Type} (step : Call → Step σ (Halt × State)) (step' : Call → Step τ (Halt × State))
    (init : Call → σ) (init' : Call → τ)
    (runs : ∀ call n, A.run o p call n = Machine.iterate (step call) n (init call))
    (runs' : ∀ call n, B.run o q call n = Machine.iterate (step' call) n (init' call))
    (cut : σ → Bool) (cut' : τ → Bool) (rels : Call → List (σ → τ → Prop))
    (start : ∀ call, scope call → ∃ P ∈ rels call, P (init call) (init' call)) {K' : Nat}
    (bounded : ∀ call, scope call → BoundedSim (step call) cut (step' call) cut' Agree
      (fun x x' => ∃ P ∈ rels call, P x x') K') :
    LayerSim A B o p q scope where
  σ := σ
  τ := τ
  step := step
  step' := step'
  init := init
  init' := init'
  runs := runs
  runs' := runs'
  cut := cut
  cut' := cut'
  Rel call := fun x x' => ∃ P ∈ rels call, P x x'
  start := start
  sim call h := (bounded call h).toSim

end SolarTV.CutPoint
