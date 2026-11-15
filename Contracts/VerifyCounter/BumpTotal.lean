import SolarTV.Termination
import Contracts.VerifyCounter.Bump

/-!
# bump's loop: termination with an explicit bound from its ranking certificate

`Bump.stage0_ends` shows every call of bump ends on solar's first lowered MIR. Here the same
certificate (the invariant and the measure `n - i` that `inferred.py` emits from
`solar-verify --show-inferred`, `Inferred.Inv` and `Inferred.rank`) is checked through the
generic termination checker `SolarTV.CutPoint.ends_within_start` with every segment's fuel
fixed at 40 blocks, which gives a bound read off the ranking: every call of bump ends within
`(n + 2) * 40` blocks of the MIR, whatever `n` is (`stage0_ends_within`). With each block
charged one unit (`stage0_gas`), a metered run with that much gas never runs out of it, and
its result is the unmetered run's (`SolarTV.CutPoint.runGas_done_run`).

The segments are checked again, conjunct by conjunct, by the symbolic procedure of `Bump`;
the rank must fall on the back edge (`i` grows, `n` is fixed) or the segment from block 10
fails by mismatch.
-/

namespace SolarTV.Milestone.VerifyCounter.Bump

open Machine SolarTV.Export.Counter SolarTV.Milestone.W1
open SolarTV.CutPoint (seg SegEnds)

/-- The first configuration of a call. -/
def start (call : Call) : MIR.Lowered.Frame :=
  ([], .enter stage0.entry 0 0, fun _ => 0, MIR.Lowered.Module.startState stage0 (State.initial call))

set_option maxHeartbeats 4000000 in
theorem wseg0 (o : Oracle) (call : Call) (hsel : IsBump call) :
    SegEnds (Inferred.Inv call) (Post call) (fun _ => True)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 (start call)) := by
  unfold IsBump at hsel
  unfold start
  total_seg

set_option maxHeartbeats 4000000 in
theorem wseg7 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at7 call env s) :
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 7 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 4 7 1, env, s)) := by
  unfold Inferred.at7 at h
  repeat obtain ⟨_, h⟩ := h
  total_seg

set_option maxHeartbeats 4000000 in
theorem wseg10 (o : Oracle) (call : Call) (env : MIR.Lowered.Env) (s : State)
    (h : Inferred.at10 call env s) :
    SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call ([], .enter 4 10 1, env, s))
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 ([], .enter 4 10 1, env, s)) := by
  unfold Inferred.at10 at h
  repeat obtain ⟨_, h⟩ := h
  total_seg

/-- Every segment from a cut point of the certificate. -/
theorem wseg (o : Oracle) (call : Call) :
    ∀ x, Inferred.Inv call x → SegEnds (Inferred.Inv call) (Post call)
      (fun y => Inferred.rank call y < Inferred.rank call x)
      (seg (MIR.Lowered.moduleBlock o call stage0) cut 40 x) := by
  rintro x (⟨env, s, rfl, h⟩ | ⟨env, s, rfl, h⟩)
  · exact wseg7 o call env s h
  · exact wseg10 o call env s h

/-- Every rank of the invariant is at most `n`. -/
theorem rank_le (call : Call) :
    ∀ y, Inferred.Inv call y → Inferred.rank call y ≤ (calldataWord call 4).toNat := by
  rintro y (⟨env, s, rfl, h⟩ | ⟨env, s, rfl, h⟩) <;> simp only [Inferred.rank] <;> omega

/-- **Every call of bump ends within `(n + 2) * 40` blocks of solar's first lowered MIR, and
meets bump's spec**, for the bound the ranking certificate gives. -/
theorem stage0_ends_within (o : Oracle) (call : Call) (hsel : IsBump call) :
    ∃ r, Machine.iterate (MIR.Lowered.moduleBlock o call stage0)
      (((calldataWord call 4).toNat + 2) * 40) (start call) = some r ∧ Post call r := by
  obtain ⟨r, ran, post⟩ := CutPoint.ends_within_start (Inferred.rank call) 40
    (calldataWord call 4).toNat (rank_le call) (wseg0 o call hsel) (wseg o call)
  exact ⟨r, by rw [CutPoint.iterate_eq]; exact ran, post⟩

/-- **The resource form**: charging each block one unit, a run with `(n + 1) * 40` units from
a cut point of the certificate never runs out, and ends meeting bump's spec. -/
theorem stage0_gas (o : Oracle) (call : Call) (x : MIR.Lowered.Frame) (hx : Inferred.Inv call x)
    (g : Nat) (hg : ((calldataWord call 4).toNat + 1) * 40 ≤ g) :
    ∃ n r left, CutPoint.runGas (MIR.Lowered.moduleBlock o call stage0) (fun _ => 1) n g x =
      some (.done r left) ∧ Post call r :=
  CutPoint.gas_ends (cut := cut) (Inferred.rank call) 40 40
    (fun y hy => ⟨wseg o call y hy, CutPoint.segCost_one_le 40 y⟩) x hx g
    (Nat.le_trans (Nat.mul_le_mul_right 40 (by have := rank_le call x hx; omega)) hg)

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.stage0_ends_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage0_ends_within

/-- info: 'SolarTV.Milestone.VerifyCounter.Bump.stage0_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stage0_gas

end SolarTV.Milestone.VerifyCounter.Bump
