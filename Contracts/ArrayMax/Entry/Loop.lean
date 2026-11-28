import Contracts.ArrayMax.Entry.Basic

/-! ArrayMaxEntry.max: the loop's segments, from its header entered from its entry and from its
back edge, with the ranking certificate's obligations (`SegEnds`): each ends in a result meeting
`Post` or back at the header with the invariant and a lower rank, and is never stuck. -/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

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

end SolarTV.Milestone.ArrayMaxEntry
