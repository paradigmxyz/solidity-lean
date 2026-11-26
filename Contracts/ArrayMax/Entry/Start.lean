import Contracts.ArrayMax.Entry.Basic

/-! ArrayMaxEntry.max: the segment from the call's start to the loop's header, with the ranking
certificate's obligations (`SegEnds`): it ends in a result meeting `Post` or at the header with
the invariant, and is never stuck. -/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- What the decoder's length check gives: a length at most the words left, so at most
`2 ^ 251 - 1`, the bound the compiler assumes when it scales the length by 32. -/
theorem le_of_not_shr5_lt {x y : EvmRules.Word} (h : ¬EvmRules.Evm.shr 5 x < y) :
    y ≤ 3618502788666131106986593281521497120414687020801267626233049500247285301247 := by
  have hs : EvmRules.Evm.shr 5 x ≤ 3618502788666131106986593281521497120414687020801267626233049500247285301247 := by
    simp only [EvmRules.Evm.shr]
    rw [show BitVec.ult (5 : EvmRules.Word) 256 = true by decide]
    simp only [Bool.cond_true, BitVec.ushiftRight_eq', BitVec.le_def, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    rw [show (5 : EvmRules.Word).toNat = 5 from rfl,
      show (3618502788666131106986593281521497120414687020801267626233049500247285301247 : EvmRules.Word).toNat =
        3618502788666131106986593281521497120414687020801267626233049500247285301247 from rfl]
    have := x.isLt
    omega
  bv_omega

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
theorem tseg0 (o : Oracle) (call : Call) (hsel : IsMax call) (fits : CalldataFits call) :
    SegEnds (Inferred.Inv call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40
        ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  unfold IsMax at hsel
  unfold CalldataFits at fits
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegEnds, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegEnds, cut_enter, cut_resume])
  all_goals first
    | rev_leaf
    | (exfalso; simp_all only [↓reduceIte, Nat.reduceBEq, Bool.false_eq_true,
        not_false_eq_true]; done)
    | bv_omega
    | ((first | refine ⟨Or.inr ⟨_, _, rfl, ?_⟩, trivial⟩ | refine Or.inr ⟨_, _, rfl, ?_⟩)
       simp only [Inferred.at10, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
         EvmRules.Evm.add, EvmRules.Evm.sub] at *
       and_intros <;> am_entry)
    | (obtain ⟨h1, -, -⟩ := ‹¬_ < _ ∧ ¬_ < _ ∧ ¬_ < _›
       have := le_of_not_shr5_lt h1
       bv_omega)

end SolarTV.Milestone.ArrayMaxEntry
