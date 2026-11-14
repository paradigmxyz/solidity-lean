import Contracts.VerifyCounter.Bump

/-!
# bump's exact ends on solar's first lowered MIR

`Bump.Post` says what bump's spec asks of a successful end. A source stage needs more: the
exact end of every call, so that its observable can be compared with SolidCore's. `PostX` is
that end, on every call of bump with no value and at least one argument word:

* `count + n` wraps: a revert with `Panic(0x11)`'s data (`panicData`);
* otherwise `count + n > limit`: a revert with `Error("over")`'s data (`overData`);
* otherwise `stop`, with slot 0 holding `count + n` and every other slot as it was.

It is proved through the same cut point and the same generated invariant (`Inferred.lean`) as
`Bump.stage0_ends`, with the same ranking certificate: only the leaves differ.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- `Panic(0x11)`'s revert data as bump's MIR writes it. -/
def panicData : List Memory.Byte := ((Mem.initial.store 32 17).store 0 0x4e487b71).read 28 36

/-- `Error("over")`'s revert data as bump's MIR writes it. -/
def overData : List Memory.Byte :=
  ((((Mem.initial.store 32 32).store 64 4).store 96
    0x6f76657200000000000000000000000000000000000000000000000000000000).store 0 0x8c379a0).read 28 100

/-- The exact end of a call of bump. -/
def PostX (call : Call) (r : Halt × State) : Prop :=
  BitVec.ofNat 256 call.callvalue = 0 → ¬ BitVec.ofNat 256 call.calldata.size < 36 →
    ((State.initial call).storage 0 + calldataWord call 4 < (State.initial call).storage 0 →
        r.1 = .revert panicData) ∧
    (¬ (State.initial call).storage 0 + calldataWord call 4 < (State.initial call).storage 0 →
        (State.initial call).storage 1 < (State.initial call).storage 0 + calldataWord call 4 →
        r.1 = .revert overData) ∧
    (¬ (State.initial call).storage 0 + calldataWord call 4 < (State.initial call).storage 0 →
        ¬ (State.initial call).storage 1 < (State.initial call).storage 0 + calldataWord call 4 →
        r.1 = .stop ∧ r.2.storage 0 = (State.initial call).storage 0 + calldataWord call 4 ∧
          ∀ k, k ≠ 0 → r.2.storage k = (State.initial call).storage k)

macro "exact_leaf" : tactic => `(tactic| (
  unfold PostX; dsimp only; intro _ _; (try simp only [EvmRules.Evm.add] at *)
  refine ⟨?_, ?_, ?_⟩ <;> intros
  all_goals first
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)
    | rfl
    | (refine ⟨?_, ?_, ?_⟩ <;> first | exact True.intro | rfl | word_goal | (intro _ _; first | exact True.intro | rfl | word_goal) | bv_omega)))

macro "xtotal_leaf" : tactic => `(tactic| (
  first
    | exact_leaf
    | (refine ⟨?_, ?_⟩
       · inv_goal
       · first | exact True.intro | rank_goal)
    | inv_goal
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)))

syntax "xtotal_seg" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| xtotal_seg) => `(tactic| (
      obtain ⟨cd, hcd⟩ : ∃ cd, cd = calldataWord call := ⟨_, rfl⟩
      bump_norm [SegEnds, cut_enter, cut_resume]
      repeat' (split_cond <;> bump_norm [SegEnds, cut_enter, cut_resume])
      all_goals xtotal_leaf))

set_option maxHeartbeats 4000000 in
theorem xseg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ k, SegEnds (Inferred.Inv call) (PostX call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  refine ⟨40, ?_⟩
  unfold IsBump at hsel
  xtotal_seg

set_option maxHeartbeats 4000000 in
theorem xseg7 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at7 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (PostX call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 7 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 7 1, env, s)) := by
  refine ⟨40, ?_⟩
  unfold Inferred.at7 at h
  repeat obtain ⟨_, h⟩ := h
  xtotal_seg

set_option maxHeartbeats 4000000 in
theorem xseg10 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (PostX call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 10 1, env, s)) := by
  refine ⟨40, ?_⟩
  unfold Inferred.at10 at h
  repeat obtain ⟨_, h⟩ := h
  xtotal_seg

/-- **Every call of bump ends on solar's first lowered MIR in its exact end** (`PostX`),
through the generated invariant and the ranking certificate `n - i`. -/
theorem xstage0_ends (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ r, MIR.Lowered.moduleLayer.Ends o stage0 call r ∧ PostX call r := by
  obtain ⟨n, r, ran, post⟩ := CutPoint.ends_of_start (Inferred.rank call) (xseg0 o call hsel) (by
    rintro x (⟨env, s, rfl, h⟩ | ⟨env, s, rfl, h⟩)
    · exact xseg7 o call env s h
    · exact xseg10 o call env s h)
  refine ⟨r, ⟨n, ?_⟩, post⟩
  change Machine.iterate _ n _ = some r
  rw [CutPoint.iterate_eq]
  exact ran

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.xstage0_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms xstage0_ends

end SolarTV.Milestone.VerifyCounter.Bump
