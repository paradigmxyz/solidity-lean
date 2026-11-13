import Contracts.ArrayMax.Entry.Basic

/-! ArrayMaxEntry.max: the loop's segments, from its header entered from its entry and from its back edge. -/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegOk)

/-! ## The segments -/

set_option maxHeartbeats 4000000 in
theorem seg10 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    ∃ k, SegOk (Inferred.Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 0 10 2, env, s)) := by
  refine ⟨20, ?_⟩
  obtain ⟨-, -, a1, a2, fa, ex, exi, lpos, -, e37, e126, -, hst, e91, e119, copy, hlen⟩ := h
  simp only [e119, e37, e91] at fa ex exi hlen a2
  have hptr : (128 : W) + 32 + 32 * 1 = 128 + 64 := by decide
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegOk, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegOk, cut_enter, cut_resume])
  all_goals first
    | exact True.intro
    | (apply post_exit (i := 1) <;> first | assumption | bv_omega)
    | (refine Or.inl ⟨_, _, rfl, ?_⟩
       simp only [Inferred.at5, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
         EvmRules.Evm.add, e119, e91]
       and_intros <;> am_conj)

set_option maxHeartbeats 4000000 in
theorem seg5 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at5 call env s) :
    ∃ k, SegOk (Inferred.Inv call) (Post call)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 0 5 2, env, s)) := by
  refine ⟨20, ?_⟩
  obtain ⟨a0, -, a1, a2, fa, ex, exi, lpos, ipos, e129, hst, e91, e119, copy, hlen⟩ := h
  simp only [e119, e91] at fa ex exi hlen
  have hptr : (128 : W) + 32 + 32 * env 51 = 128 + 64 + 32 * (env 51 - 1) := by bv_omega
  obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
  seg_norm [SegOk, cut_enter, cut_resume]
  repeat' (split_cond <;> seg_norm [SegOk, cut_enter, cut_resume])
  all_goals first
    | exact True.intro
    | (apply post_exit (i := env 51) <;> first | assumption | bv_omega)
    | (refine Or.inl ⟨_, _, rfl, ?_⟩
       simp only [Inferred.at5, MIR.Lowered.Env.set, Mem.load_expand, ↓reduceIte, Nat.reduceEqDiff,
         EvmRules.Evm.add, e119, e91]
       and_intros <;> am_conj)

end SolarTV.Milestone.ArrayMaxEntry
