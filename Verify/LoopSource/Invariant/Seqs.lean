import Verify.LoopSource.Invariant.While
import Verify.LoopSource.Equiv.Seq

/-!
# A `while` loop's obligations as sequents over words

`Invariant.Obl` (`Invariant/While.lean`) is a statement about every header valuation. This module
states it as a finite list of sequents (`Inv.Seq`, the formulas over words that the cut-point
route's `Seq.Valid` and `wordnorm` already decide), so a generator can emit the obligations of a
proposed invariant and measure as data and the kernel can check each sequent on its own:

* the invariant is a list of formulas `I : List Inv.F` over the header valuation `σ` (its words
  below `base` are the call's, the words `base + j` are the header's fresh words), and the measure
  is a word `μ` over `σ` (`InvP I`, `measP μ`);
* `whileSeqs E wd I μ` lists, under the call's facts `E.facts`:
  - initiation: each formula of `I` with the fresh words replaced by the words before the loop
    (`instF … θ0`);
  - exit: under `I` and a zero condition, each fresh word `base + j` equals `exitθ j`;
  - guards: under `I` and a nonzero condition, each overflow guard of the body is zero;
  - preservation: under `I` and a nonzero condition, each formula of `I` with the fresh words
    replaced by their step (`instF … step`);
  - descent: under the same hypotheses, the measure after the step is below the measure;
* it is `none` unless the facts and every exit word mention only the call's words (below `base`),
  which is what lets a sequent over `σ` speak of the call valuation;
* the measure's bound below `loopFuel` needs no sequent: every word is below `2 ^ 256`.

`obl_of_whileSeqs`: when every sequent is valid, `Obl E wd (InvP I) (measP μ)` holds. The sequents
are untrusted data: only their validity, proved in the kernel, counts.
-/

namespace Verify.LoopSource.Invariant
open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop
open Verify.LoopSource.Equiv.Inv (F Seq factsF factsF_holds)

/-! ## Formulas with the fresh words replaced -/

/-- `instW` on every word of a formula. -/
def instF (base len : Nat) (θ : Nat → WExpr) : F → F
  | .fact e b => .fact (instW base len θ e) b
  | .le a b => .le (instW base len θ a) (instW base len θ b)
  | .lt a b => .lt (instW base len θ a) (instW base len θ b)
  | .eq a b => .eq (instW base len θ a) (instW base len θ b)
  | .lin a b c d =>
    .lin (instW base len θ a) (instW base len θ b) (instW base len θ c) (instW base len θ d)
  | .or f g => .or (instF base len θ f) (instF base len θ g)
  | .not f => .not (instF base len θ f)

/-- **A formula with the fresh words replaced holds where the formula holds at the extended
valuation.** -/
theorem holds_instF (ρ : Val) (base len : Nat) (θ : Nat → WExpr) : ∀ f : F,
    (instF base len θ f).Holds ρ ↔ f.Holds (extV ρ base len fun j => (θ j).eval ρ)
  | .fact e b => by simp only [instF, F.Holds, eval_instW]
  | .le a b => by simp only [instF, F.Holds, eval_instW]
  | .lt a b => by simp only [instF, F.Holds, eval_instW]
  | .eq a b => by simp only [instF, F.Holds, eval_instW]
  | .lin a b c d => by simp only [instF, F.Holds, eval_instW]
  | .or f g => by simp only [instF, F.Holds, holds_instF ρ base len θ f, holds_instF ρ base len θ g]
  | .not f => by simp only [instF, F.Holds, holds_instF ρ base len θ f]

/-! ## The sequents -/

/-- The invariant of a formula list: every formula holds at the header valuation. -/
def InvP (I : List F) (_ρ σ : Val) : Prop := ∀ f ∈ I, f.Holds σ

/-- The measure of a word: its value at the header valuation. -/
def measP (μ : WExpr) (_ρ σ : Val) : Nat := μ.eval σ

namespace WhileData

/-- The word fresh word `j` holds before the loop. -/
def θ0 (wd : WhileData) (j : Nat) : WExpr := (entries wd.S1 wd.slots).getD j (.lit 0)

end WhileData

/-- Initiation: each formula of `I` at the words before the loop. -/
def initSeqs (E : EraseEnv) (wd : WhileData) (I : List F) : List Seq :=
  I.map fun g => (factsF E.facts, some (instF (wd.base E) wd.len wd.θ0 g))

/-- Exit: where `I` holds and the condition is zero, fresh word `j` is `exitθ j`. -/
def exitSeqs (E : EraseEnv) (wd : WhileData) (I : List F) : List Seq :=
  (List.range wd.len).map fun j =>
    (factsF E.facts ++ I ++ [.fact wd.c false], some (.eq (.arg (wd.base E + j)) (wd.exitθ j)))

/-- The hypotheses of an iteration: the facts, `I` and a nonzero condition. -/
def iterHyps (E : EraseEnv) (wd : WhileData) (I : List F) : List F :=
  factsF E.facts ++ I ++ [.fact wd.c true]

/-- No overflow guard of the body fires. -/
def guardSeqs (E : EraseEnv) (wd : WhileData) (I : List F) : List Seq :=
  wd.gs.map fun g => (iterHyps E wd I, some (.fact g false))

/-- Preservation: each formula of `I` after the step. -/
def presSeqs (E : EraseEnv) (wd : WhileData) (I : List F) : List Seq :=
  I.map fun g => (iterHyps E wd I, some (instF (wd.base E) wd.len wd.step g))

/-- Descent: the measure after the step is below the measure. -/
def decSeq (E : EraseEnv) (wd : WhileData) (I : List F) (μ : WExpr) : Seq :=
  (iterHyps E wd I, some (.lt (instW (wd.base E) wd.len wd.step μ) μ))

/-- **The sequents of a `while` loop's data** for the invariant `I` and the measure `μ`: `none`
unless the facts and the exit words mention only the call's words. -/
def whileSeqs (E : EraseEnv) (wd : WhileData) (I : List F) (μ : WExpr) : Option (List Seq) :=
  if factsBelow (wd.base E) E.facts &&
      (List.range wd.len).all (fun j => belowW (wd.base E) (wd.exitθ j)) then
    some (initSeqs E wd I ++ exitSeqs E wd I ++ guardSeqs E wd I ++ presSeqs E wd I ++
      [decSeq E wd I μ])
  else none

/-! ## Soundness -/

/-- A valid sequent's goal holds where its hypotheses do. -/
theorem goal_of {hs : List F} {g : F} (h : Seq.Valid (hs, some g)) {σ : Val}
    (hh : ∀ f ∈ hs, f.Holds σ) : g.Holds σ := h σ hh

/-- The hypotheses of an iteration hold at the header valuation of the words `f`. -/
theorem iterHyps_holds {E : EraseEnv} {wd : WhileData} {I : List F} {ρ : Val} {f : Nat → Nat}
    (hK : factsBelow (wd.base E) E.facts = true) (hfacts : E.facts.Hold ρ)
    (hI : InvP I ρ (wd.at_ E ρ f)) (hnz : wd.c.eval (wd.at_ E ρ f) ≠ 0) :
    ∀ g ∈ iterHyps E wd I, g.Holds (wd.at_ E ρ f) := by
  intro g hg
  simp only [iterHyps, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | hg) | rfl
  · exact factsF_holds ((hold_extV ρ _ _ f hK).mpr hfacts) g hg
  · exact hI g hg
  · simp only [F.Holds]
    exact ⟨fun h => absurd h hnz, fun h => by cases h⟩

/-- The header valuation after the step is the header valuation of the step's words. -/
theorem extV_step (E : EraseEnv) (wd : WhileData) (ρ : Val) (f : Nat → Nat) :
    extV (wd.at_ E ρ f) (wd.base E) wd.len (fun j => (wd.step j).eval (wd.at_ E ρ f)) =
      wd.at_ E ρ (wd.stepV (wd.at_ E ρ f)) :=
  extV_extV ρ _ _ _ _

/-- **Valid sequents give the loop's obligations.** -/
theorem obl_of_whileSeqs {E : EraseEnv} {wd : WhileData} {I : List F} {μ : WExpr}
    {ss : List Seq} (h : whileSeqs E wd I μ = some ss) (hv : ∀ s ∈ ss, s.Valid) :
    Obl E wd (InvP I) (measP μ) := by
  unfold whileSeqs at h
  split at h
  · rename_i hb
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
    obtain ⟨hK, hX⟩ := hb
    cases h
    have vI : ∀ s ∈ initSeqs E wd I, s.Valid := fun s hs => hv s (by simp [hs])
    have vX : ∀ s ∈ exitSeqs E wd I, s.Valid := fun s hs => hv s (by simp [hs])
    have vG : ∀ s ∈ guardSeqs E wd I, s.Valid := fun s hs => hv s (by simp [hs])
    have vP : ∀ s ∈ presSeqs E wd I, s.Valid := fun s hs => hv s (by simp [hs])
    have vD : (decSeq E wd I μ).Valid := hv _ (by simp)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ρ _ hfacts g hg
      have hs := vI _ (List.mem_map_of_mem (f := fun g => (factsF E.facts,
        some (instF (wd.base E) wd.len wd.θ0 g))) hg)
      exact (holds_instF ρ _ _ _ g).mp (goal_of hs (factsF_holds hfacts))
    · intro ρ _ _
      show _ < 2 ^ 256 + 1
      exact Nat.lt_succ_of_lt (WExpr.eval_lt _ _)
    · intro ρ f _ hfacts hf hI hz j hj
      have hs := vX _ (List.mem_map_of_mem (f := fun j =>
        (factsF E.facts ++ I ++ [.fact wd.c false],
          some (F.eq (.arg (wd.base E + j)) (wd.exitθ j)))) (List.mem_range.mpr hj))
      have hh : ∀ g ∈ factsF E.facts ++ I ++ [.fact wd.c false], g.Holds (wd.at_ E ρ f) := by
        intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | hg) | rfl
        · exact factsF_holds ((hold_extV ρ _ _ f hK).mpr hfacts) g hg
        · exact hI g hg
        · simp only [F.Holds]
          exact ⟨fun _ => trivial, fun _ => hz⟩
      have he := goal_of hs hh
      simp only [F.Holds] at he
      rw [WhileData.at_, arg_extV ρ _ _ f hj (hf j),
        eval_extV_below ρ _ _ f _ (hX j hj)] at he
      exact he
    · intro ρ f _ hfacts _ hI hnz g hg
      have hs := vG _ (List.mem_map_of_mem (f := fun g =>
        (iterHyps E wd I, some (F.fact g false))) hg)
      have he := goal_of hs (iterHyps_holds hK hfacts hI hnz)
      simp only [F.Holds] at he
      exact he.mpr trivial
    · intro ρ f _ hfacts _ hI hnz g hg
      have hs := vP _ (List.mem_map_of_mem (f := fun g =>
        (iterHyps E wd I, some (instF (wd.base E) wd.len wd.step g))) hg)
      have he := (holds_instF _ _ _ _ g).mp (goal_of hs (iterHyps_holds hK hfacts hI hnz))
      rw [extV_step] at he
      exact he
    · intro ρ f _ hfacts _ hI hnz
      have he := goal_of vD (iterHyps_holds hK hfacts hI hnz)
      simp only [F.Holds, eval_instW] at he
      rw [extV_step] at he
      exact he
  · cases h

end Verify.LoopSource.Invariant

/-- info: 'Verify.LoopSource.Invariant.obl_of_whileSeqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Verify.LoopSource.Invariant.obl_of_whileSeqs
