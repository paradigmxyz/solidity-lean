import Contracts.VerifyCounter.Bump
import Verify.Eval.G.Capture.Hook

/-!
# Lane G: capture the leaves of bump's generated loop proof

Contracts/VerifyCounter/Bump.lean proves bump's loop on solar's MIR through the GENERATED invariant
(Inferred.lean); every segment ends in leaves that total_leaf closes. Here a newer macro_rules for
total_leaf (tried first) prints each leaf, with its local context, as a standalone theorem
(Hook.goalText), runs total_leaf's own body (copied verbatim below as total_leaf_orig), and
records whether it closed the leaf and how long it took, appending to G_CAPTURE_OUT with the tag
LEAF. tseg0, tseg7 and tseg10 are Bump.lean's, verbatim but for their names; the back-edge segment
under BumpWrongRank.lean's growing rank (copied) is the negative: its rank leaf must fail. The
sym_mem side conditions of the same runs are captured too (Hook), tagged CAPTURE.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

-- Bump.lean's opens, before the macros as there (macro names resolve where they are defined).
open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- total_leaf's body in Bump.lean, verbatim. -/
macro "total_leaf_orig" : tactic => `(tactic| (
  first
    | (unfold Post; dsimp only; intro h; rcases h with h | ⟨_, h⟩ <;> exact Halt.noConfusion h)
    | (unfold Post; dsimp only; intro _; (try simp only [EvmRules.Evm.add] at *);
        refine ⟨?_, ?_, ?_, ?_⟩ <;> word_goal)
    | (refine ⟨?_, ?_⟩
       · inv_goal
       · first | exact True.intro | rank_goal)
    | inv_goal
    | (exfalso; bv_omega)
    | (exfalso; sym_omega)))

syntax "g_leaf_capture" : tactic

open Lean Elab Tactic in
@[tactic «tacticG_leaf_capture»] def gLeafCapture : Tactic := fun _ => do
  let g ← getMainGoal
  let txt ← withoutModifyingState <| withOptions (fun o => (pp.fullNames.set (pp.numericTypes.set
    (pp.funBinderTypes.set (pp.proofs.set (pp.deepTerms.set (pp.maxSteps.set o 100000000) true) true)
    true) true) true)) <| Verify.Eval.G.Capture.goalText g
  let t0 ← IO.monoNanosNow
  let (ok, err) ← try
      withoutRecover (evalTactic (← `(tactic| total_leaf_orig)))
      pure (true, "")
    catch e => pure (false, ← e.toMessageData.toString)
  let t1 ← IO.monoNanosNow
  let out := (← IO.getEnv "G_CAPTURE_OUT").getD "/tmp/g-capture.txt"
  let h ← IO.FS.Handle.mk out .append
  h.putStrLn s!"LEAF ok={ok} ms={(t1 - t0).toFloat / 1000000.0}\n{txt}\nENDLEAF"
  h.flush
  unless ok do throw (Exception.error .missing (m!"total_leaf failed: {err.take 200}"))

macro_rules | `(tactic| total_leaf) => `(tactic| g_leaf_capture)

set_option maxHeartbeats 4000000 in
theorem tseg0_g (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))) := by
  refine ⟨40, ?_⟩
  unfold IsBump at hsel
  total_seg

set_option maxHeartbeats 4000000 in
theorem tseg7_g (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at7 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 7 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 7 1, env, s)) := by
  refine ⟨40, ?_⟩
  unfold Inferred.at7 at h
  repeat obtain ⟨_, h⟩ := h
  total_seg

set_option maxHeartbeats 4000000 in
theorem tseg10_g (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    ∃ k, SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut k ([], .enter 4 10 1, env, s)) := by
  refine ⟨40, ?_⟩
  unfold Inferred.at10 at h
  repeat obtain ⟨_, h⟩ := h
  total_seg

/-- BumpWrongRank.lean's growing rank and back-edge obligation, verbatim. -/
def growing_g (x : MIR.Lowered.Frame) : Nat := (x.2.2.1 20).toNat

def BackEdge_g (R : Call → MIR.Lowered.Frame → Nat) : Prop :=
  ∀ (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State),
    Inferred.at10 call env s →
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => R call y < R call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 4 10 1, env, s))

set_option maxHeartbeats 4000000 in
theorem growing_rejected_g : True := by
  fail_if_success
    have : BackEdge_g (fun _ => growing_g) := by
      intro o call env s h
      have hr : ∀ x, growing_g x = (x.2.2.1 20).toNat := fun _ => rfl
      unfold Inferred.at10 at h
      repeat obtain ⟨_, h⟩ := h
      total_seg
  trivial

end SolarTV.Milestone.VerifyCounter.Bump
