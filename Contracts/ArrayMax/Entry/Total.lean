import SolarTV.Termination
import Contracts.ArrayMax.Entry.Loop
import Contracts.ArrayMax.Entry.Start

/-!
# ArrayMaxEntry.max ends: the loop's ranking certificate, checked

The loop's invariant, with the measure `xs.length - i` that
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
