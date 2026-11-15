import Contracts.VerifyCounter.BumpTotal

/-!
# A ranking certificate that does not fall is rejected

The negative control for `BumpTotal`. The segment of bump's loop from its back edge is checked
twice by one script, which differs only in the rank it is given:

* `falling`, `n - i` read off the frame (the inferred measure): accepted
  (`falling_accepted`);
* `growing`, `i` read off the frame, which grows on every iteration: the rank obligation
  `i + 2 < i + 1` is false, the leaf tactic fails at once (no timeout), and `fail_if_success`
  makes this file build only while the wrong certificate is rejected (`growing_rejected`).
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- The loop variable `i` at the header, read off the frame: it grows. -/
def growing (x : MIR.Lowered.Frame) : Nat := (x.2.2.1 20).toNat

/-- `n - i`, read off the frame the same way: it falls. -/
def falling (call : Call) (x : MIR.Lowered.Frame) : Nat :=
  (calldataWord call 4).toNat - (x.2.2.1 20).toNat

/-- The segment obligation from the back edge with a rank `R`. -/
def BackEdge (R : Call → MIR.Lowered.Frame → Nat) : Prop :=
  ∀ (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State),
    Inferred.at10 call env s →
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => R call y < R call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 4 10 1, env, s))

set_option maxHeartbeats 4000000 in
theorem falling_accepted : BackEdge falling := by
  intro o call env s h
  have hr : ∀ x, falling call x = (calldataWord call 4).toNat - (x.2.2.1 20).toNat := fun _ => rfl
  unfold Inferred.at10 at h
  repeat obtain ⟨_, h⟩ := h
  total_seg

set_option maxHeartbeats 4000000 in
theorem growing_rejected : True := by
  fail_if_success
    have : BackEdge (fun _ => growing) := by
      intro o call env s h
      have hr : ∀ x, growing x = (x.2.2.1 20).toNat := fun _ => rfl
      unfold Inferred.at10 at h
      repeat obtain ⟨_, h⟩ := h
      total_seg
  trivial

end SolarTV.Milestone.VerifyCounter.Bump
