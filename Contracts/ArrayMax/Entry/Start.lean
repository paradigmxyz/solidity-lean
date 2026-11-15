import Contracts.ArrayMax.Entry.Basic

/-! ArrayMaxEntry.max: the segment from the call's start to the loop's header. -/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegOk)

/-- One conjunct of the invariant at the loop's entry. -/
syntax "am_entry" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| am_entry) => `(tactic| first
    | rfl
    | assumption
    | exact BitVec.le_refl _
    | (intro j hj; have : j = 0 := by bv_omega
       subst this; exact BitVec.le_refl _)
    | exact ⟨0, by bv_omega, rfl⟩
    | (obtain ⟨hC, hA, hB⟩ := ‹¬_ < _ ∧ ¬_ < _ ∧ ¬_ < _›
       exact copy_entry call _ fits hA hB hC)
    | (rw [show (128 : W).toNat = 128 from rfl, load_write_below _ _ _ _ _ (by decide),
        Mem.load_store_same])
    | bv_omega
    | (simp only [EvmRules.Evm.gt, BitVec.ult, Bool.cond_eq_ite, decide_eq_true_eq]; split <;> bv_omega))

set_option maxHeartbeats 8000000 in
theorem seg0 (o : Oracle) (call : Call) (hsel : IsMax call) (fits : CalldataFits call) :
    ∃ k, SegOk (Inferred.Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k
        ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  refine ⟨40, ?_⟩
  unfold IsMax at hsel
  unfold CalldataFits at fits
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegOk, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegOk, cut_enter, cut_resume])
  all_goals first
    | exact True.intro
    | rev_leaf
    | (exfalso; simp_all only [↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
        not_false_eq_true]; done)
    | (refine Or.inr ⟨_, _, rfl, ?_⟩
       simp only [Inferred.at10, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
         EvmRules.Evm.add, EvmRules.Evm.sub] at *
       and_intros <;> am_entry)

end SolarTV.Milestone.ArrayMaxEntry
