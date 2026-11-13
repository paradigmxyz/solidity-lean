import SolarTV.Termination
import Contracts.ArrayMax.Entry.Basic

/-!
# ArrayMaxEntry.max ends: the loop's ranking certificate, checked

`Entry.stage0_post` is partial correctness: every end of the first lowered MIR on a call of
`max` meets `Post`. Here the same invariant, with the measure `xs.length - i` that
`inferred.py` emits from `solar-verify --show-inferred` (`Inferred.rank`), goes through the
generic termination checker `SolarTV.CutPoint.ends_within_start`: every segment must end in a
result meeting `Post` or at the header with the invariant and a lower rank, and none may be
stuck. So every call of `max` (with calldata the EVM can pay for, `CalldataFits`) ends within
`(xs.length + 2) * 40` blocks of the MIR, whatever the array's length, and meets `Post`
(`stage0_ends_within`), and a metered run from the header with `(xs.length + 1) * 40` units never
runs out (`stage0_gas`).
-/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- The array's length, as the rank reads it. -/
abbrev lenN (call : Call) : Nat :=
  (calldataWord call (calldataWord call 4 + (4 : EvmRules.Word))).toNat

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
syntax "am_entry'" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| am_entry') => `(tactic| first
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
       and_intros <;> am_entry')
    | (obtain ⟨h1, -, -⟩ := ‹¬_ < _ ∧ ¬_ < _ ∧ ¬_ < _›
       have := le_of_not_shr5_lt h1
       bv_omega)

set_option maxHeartbeats 4000000 in
theorem tseg10 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 0 10 2, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 0 10 2, env, s)) := by
  obtain ⟨-, -, a1, a2, fa, ex, exi, lpos, -, e37, e126, -, hst, e91, e119, e12, copy, hlen⟩ := h
  simp only [e119, e37, e91] at fa ex exi hlen a2
  have hptr : (128 : W) + 32 + 32 * 1 = 128 + 64 := by decide
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegEnds, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegEnds, cut_enter, cut_resume])
  all_goals first
    | (apply post_exit (i := 1) <;> first | assumption | bv_omega)
    | (constructor
       · refine Or.inl ⟨_, _, rfl, ?_⟩
         simp only [Inferred.at5, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
           EvmRules.Evm.add, e119, e91]
         and_intros <;> am_conj
       · simp only [Inferred.rank, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff,
           EvmRules.Evm.add]
         bv_omega)

set_option maxHeartbeats 4000000 in
theorem tseg5 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at5 call env s) :
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 0 5 2, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 0 5 2, env, s)) := by
  obtain ⟨a0, -, a1, a2, fa, ex, exi, lpos, ipos, e129, hst, e91, e119, e12, copy, hlen⟩ := h
  simp only [e119, e91] at fa ex exi hlen
  have hptr : (128 : W) + 32 + 32 * env 51 = 128 + 64 + 32 * (env 51 - 1) := by bv_omega
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegEnds, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegEnds, cut_enter, cut_resume])
  all_goals first
    | bv_omega
    | (apply post_exit (i := env 51) <;> first | assumption | bv_omega)
    | (constructor
       · refine Or.inl ⟨_, _, rfl, ?_⟩
         simp only [Inferred.at5, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
           EvmRules.Evm.add, e119, e91]
         and_intros <;> am_conj
       · simp only [Inferred.rank, MIR.Lowered.Env.set, ↓reduceIte, Nat.reduceEqDiff,
           EvmRules.Evm.add]
         bv_omega)

/-- Every segment from a cut point of the certificate. -/
theorem tseg (o : Oracle) (call : Call) :
    ∀ x, Inferred.Inv call x → SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call x)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 x) := by
  rintro x (⟨env, s, rfl, h⟩ | ⟨env, s, rfl, h⟩)
  · exact tseg5 o call env s h
  · exact tseg10 o call env s h

theorem rank_le (call : Call) : ∀ y, Inferred.Inv call y → Inferred.rank call y ≤ lenN call := by
  rintro y (⟨env, s, rfl, h⟩ | ⟨env, s, rfl, h⟩) <;> simp only [Inferred.rank, lenN] <;> omega

/-- **Every call of `max` ends within `(xs.length + 2) * 40` blocks of solar's first lowered MIR,
and meets `Post`**: the bound the ranking certificate gives, whatever the array's length. -/
theorem stage0_ends_within (o : Oracle) (call : Call) (hsel : IsMax call) (fits : CalldataFits call) :
    ∃ r, Machine.iterate (MIR.Lowered.moduleBlock o call stage0) ((lenN call + 2) * 40)
      ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call)) =
      some r ∧ Post call r := by
  obtain ⟨r, ran, post⟩ := CutPoint.ends_within_start (Inferred.rank call) 40 (lenN call)
    (rank_le call) (tseg0 o call hsel fits) (tseg o call)
  exact ⟨r, by rw [CutPoint.iterate_eq]; exact ran, post⟩

/-- Every call of `max` ends on the MIR, in an end meeting `Post`. -/
theorem stage0_ends (o : Oracle) (call : Call) (hsel : IsMax call) (fits : CalldataFits call) :
    ∃ r, MIR.Lowered.moduleLayer.Ends o stage0 call r ∧ Post call r := by
  obtain ⟨r, ran, post⟩ := stage0_ends_within o call hsel fits
  exact ⟨r, ⟨_, by change Machine.iterate _ _ _ = some r; exact ran⟩, post⟩

/-- **The resource form**: charging each block one unit, a metered run from the header with
`(xs.length + 1) * 40` units never runs out, and ends meeting `Post`. -/
theorem stage0_gas (o : Oracle) (call : Call) (x : MIR.Lowered.Frame) (hx : Inferred.Inv call x)
    (g : Nat) (hg : (lenN call + 1) * 40 ≤ g) :
    ∃ n r left, CutPoint.runGas (MIR.Lowered.moduleBlock o call stage0) (fun _ => 1) n g x =
      some (.done r left) ∧ Post call r :=
  CutPoint.gas_ends (cut := cut) (Inferred.rank call) 40 40
    (fun y hy => ⟨tseg o call y hy, CutPoint.segCost_one_le 40 y⟩) x hx g
    (Nat.le_trans (Nat.mul_le_mul_right 40 (by have := rank_le call x hx; omega)) hg)

/-- info: 'SolarTV.Milestone.ArrayMaxEntry.stage0_ends_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage0_ends_within

/-- info: 'SolarTV.Milestone.ArrayMaxEntry.stage0_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage0_gas

end SolarTV.Milestone.ArrayMaxEntry
