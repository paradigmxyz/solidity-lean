import Verify.LoopSource.Generic.Interface
import W1Proofs.Stage
import SolarTV.Composition

/-!
# Fixed fuel for a loop: from a loop record's steps to a run that ends within a fixed fuel

A `stage_of_runs` stage needs one fuel at which the first program ends on every call in scope.
For straight-line code that fuel is the program's block count. For a loop, the block count of a
run depends on the call. This module bounds it by one number, from the loop route's record
(`Verify.LoopSource.Interface.LoopRecord`, consumed as published, not restated).

The machine side of a loop is a **bridge** (`Bridge`): a relation `At` between header valuations
of the record and machine configurations at the loop's header, such that
* from the header, when the record's invariant holds and its condition is nonzero, the machine
  reaches the header again within `B` steps, at a valuation that is one `LoopRecord.Step` on
  (`Bridge.iter`);
* from the header, when the condition is zero, the machine ends within `X` steps (`Bridge.done`).

A bridge gives, from every header configuration, `n` steps of the record (`LoopRecord.Steps`)
together with a run that ends within `n * B + X` steps (`Bridge.runs`). Since no chain of steps
is longer than the entry valuation's measure (`LoopRecord.steps_le`), a measure bound `M` on
the entry valuations of the calls in scope gives the fixed fuel `E + M * B + X`, where `E`
bounds the steps from the program's entry to the header (`fixedFuel`, `Loops`,
`ends_of_loops`). For the EVM IR layer that fuel discharges the `ends` premise of
`stage_of_runs` (`ends_fixed`, `stage_of_runs_fixed`).

Everything here is generic over the step function and the record: nothing names a contract, a
program or a file. The machine is deterministic, so `Bridge.iter` produces the step the machine
takes; the record's `Step` is only its specification. Nested loops are outside this module: one
record, one header.
-/

namespace Verify.Gas.FixedFuel

open Verify.LoopSource.Interface
open SolidCore.Refinement.Generic (Val)

/-- A run's end, as `SolarTV.Machine.iterate` returns it. -/
abbrev Res := SolarTV.Machine.Halt × SolarTV.Machine.State

variable {ς : Type}

/-- `Reach step j x y`: `j` steps from `x` continue, without ending, to `y`. -/
inductive Reach (step : ς → Option (Res ⊕ ς)) : Nat → ς → ς → Prop
  | refl (x : ς) : Reach step 0 x x
  | cont {x y z : ς} {j : Nat} : step x = some (.inr y) → Reach step j y z → Reach step (j + 1) x z

/-- `Within step k x y`: at most `k` steps from `x` continue to `y`. -/
def Within (step : ς → Option (Res ⊕ ς)) (k : Nat) (x y : ς) : Prop :=
  ∃ j, j ≤ k ∧ Reach step j x y

theorem iterate_mono_le {step : ς → Option (Res ⊕ ς)} {n m : Nat} {x : ς} {r : Res}
    (le : n ≤ m) (h : SolarTV.Machine.iterate step n x = some r) :
    SolarTV.Machine.iterate step m x = some r := by
  induction le with
  | refl => exact h
  | step _ ih => exact SolarTV.Machine.iterate_mono step _ x r ih

/-- **Steps that continue, then a run that ends**: the run from the start ends with the same
result, at the sum of the fuels. -/
theorem iterate_of_reach {step : ς → Option (Res ⊕ ς)} {j n : Nat} {x y : ς} {r : Res}
    (h : Reach step j x y) (hr : SolarTV.Machine.iterate step n y = some r) :
    SolarTV.Machine.iterate step (j + n) x = some r := by
  induction h generalizing n with
  | refl => simpa using hr
  | @cont x y z j hs _ ih =>
    rw [Nat.add_right_comm]
    simp only [SolarTV.Machine.iterate, hs]
    exact ih hr

theorem iterate_of_within {step : ς → Option (Res ⊕ ς)} {k n : Nat} {x y : ς} {r : Res}
    (h : Within step k x y) (hr : SolarTV.Machine.iterate step n y = some r) :
    SolarTV.Machine.iterate step (k + n) x = some r := by
  obtain ⟨j, hj, hre⟩ := h
  exact iterate_mono_le (by omega) (iterate_of_reach hre hr)

/-- **The machine side of a loop record**: header configurations related to header valuations,
at most `B` steps per iteration and at most `X` steps from the header to the end once the
condition is zero. -/
structure Bridge (L : LoopRecord) (step : ς → Option (Res ⊕ ς)) (B X : Nat) where
  /-- The machine is at the loop's header, at this valuation of the record's header words. -/
  At : Val → ς → Prop
  /-- An iteration: one step of the record, the header again within `B` steps. -/
  iter : ∀ {σ : Val} {x : ς}, At σ x → L.P σ → L.c.eval σ ≠ 0 →
    ∃ σ' x', L.Step σ σ' ∧ At σ' x' ∧ Within step B x x'
  /-- The exit: the run ends within `X` steps. -/
  done : ∀ {σ : Val} {x : ς}, At σ x → L.P σ → L.c.eval σ = 0 →
    ∃ r, SolarTV.Machine.iterate step X x = some r

namespace Bridge

variable {L : LoopRecord} {step : ς → Option (Res ⊕ ς)} {B X : Nat}

/-- **The run a bridge gives**: from a header configuration of the invariant, `n` steps of the
record and a run that ends within `n * B + X` steps. -/
theorem runs (Bd : Bridge L step B X) {k : Nat} {σ : Val} {x : ς} (hk : L.m σ ≤ k)
    (hx : Bd.At σ x) (hp : L.P σ) :
    ∃ n, L.Steps n σ ∧ ∃ r, SolarTV.Machine.iterate step (n * B + X) x = some r := by
  induction k generalizing σ x with
  | zero =>
    by_cases hc : L.c.eval σ = 0
    · obtain ⟨r, hr⟩ := Bd.done hx hp hc
      exact ⟨0, .done σ, r, by simpa using hr⟩
    · obtain ⟨σ', x', hs, -, -⟩ := Bd.iter hx hp hc
      have := hs.2.2.2
      omega
  | succ k ih =>
    by_cases hc : L.c.eval σ = 0
    · obtain ⟨r, hr⟩ := Bd.done hx hp hc
      exact ⟨0, .done σ, r, by simpa using hr⟩
    · obtain ⟨σ', x', hs, hx', hw⟩ := Bd.iter hx hp hc
      have hm := hs.2.2.2
      obtain ⟨n, hn, r, hr⟩ := ih (by omega) hx' hs.2.2.1
      refine ⟨n + 1, .step hs hn, r, ?_⟩
      have h1 := iterate_of_within hw hr
      have e : (n + 1) * B + X = B + (n * B + X) := by rw [Nat.succ_mul]; omega
      rw [e]
      exact h1

/-- **The run ends within a measure bound's fuel**: when the entry valuation's measure is at most
`M`, the run from the header ends within `M * B + X` steps. -/
theorem ends_within (Bd : Bridge L step B X) {σ : Val} {x : ς} (hx : Bd.At σ x) (hp : L.P σ)
    {M : Nat} (hM : L.m σ ≤ M) :
    ∃ r, SolarTV.Machine.iterate step (M * B + X) x = some r := by
  obtain ⟨n, hn, r, hr⟩ := Bd.runs (Nat.le_refl _) hx hp
  have hle : n ≤ M := Nat.le_trans (LoopRecord.steps_le hn) hM
  exact ⟨r, iterate_mono_le (Nat.add_le_add_right (Nat.mul_le_mul_right B hle) X) hr⟩

end Bridge

/-- **The fixed fuel of a loop**: `E` steps to the header, at most `M` iterations of at most `B`
steps, and at most `X` steps from the header to the end. -/
def fixedFuel (E B X M : Nat) : Nat := E + M * B + X

/-- **The fuel of a run of `n` iterations is at most the fixed fuel**: the premise is the
record's own chain of steps, so `n` is at most the entry valuation's measure. -/
theorem fuel_of_steps {L : LoopRecord} {n : Nat} {σ : Val} (hs : L.Steps n σ) {M : Nat}
    (hM : L.m σ ≤ M) (E B X : Nat) : E + n * B + X ≤ fixedFuel E B X M := by
  have hle : n ≤ M := Nat.le_trans (LoopRecord.steps_le hs) hM
  unfold fixedFuel
  have := Nat.mul_le_mul_right B hle
  omega

/-- **A program whose one loop has a bridge**: from `init`, the header within `E` steps, at a
valuation of the invariant whose measure is at most `M`. -/
def Loops (step : ς → Option (Res ⊕ ς)) (init : ς) (L : LoopRecord) (E B X M : Nat) : Prop :=
  ∃ Bd : Bridge L step B X, ∃ σ0 x, Within step E init x ∧ Bd.At σ0 x ∧ L.P σ0 ∧ L.m σ0 ≤ M

/-- **The run from the entry ends within the fixed fuel.** -/
theorem ends_of_loops {step : ς → Option (Res ⊕ ς)} {init : ς} {L : LoopRecord}
    {E B X M : Nat} (h : Loops step init L E B X M) :
    ∃ r, SolarTV.Machine.iterate step (fixedFuel E B X M) init = some r := by
  obtain ⟨Bd, σ0, x, hw, hx, hp, hM⟩ := h
  obtain ⟨r, hr⟩ := Bd.ends_within hx hp hM
  refine ⟨r, ?_⟩
  have := iterate_of_within hw hr
  unfold fixedFuel
  rwa [Nat.add_assoc]

open SolarTV.Machine

/-- **The fixed-fuel `ends` premise of `stage_of_runs`** for the EVM IR layer: every call in
scope ends within the fixed fuel. -/
theorem ends_fixed {o : SolarTV.Machine.Oracle} {p : SolarTV.EVM.Program.layer.Prog} {scope : SolarTV.Call → Prop}
    {L : LoopRecord} {E B X M : Nat}
    (loops : ∀ call, scope call →
      Loops (SolarTV.EVM.Program.block o call p) (0, [], SolarTV.Machine.State.initial call) L E B X M) :
    ∀ call, scope call → (SolarTV.EVM.Program.layer.run o p call (fixedFuel E B X M)).isSome = true := by
  intro call hc
  obtain ⟨r, hr⟩ := ends_of_loops (loops call hc)
  change (iterate (SolarTV.EVM.Program.block o call p) (fixedFuel E B X M)
    (0, [], SolarTV.Machine.State.initial call)).isSome = true
  rw [hr]
  rfl

/-- **`stage_of_runs` at the fixed fuel**: a stage from a loop's EVM IR to a second program that
gives the same result at fuel `m`, with no fuel premise beyond the bridge. -/
theorem stage_of_runs_fixed {Bl : SolarTV.Machine.Layer} {o : SolarTV.Machine.Oracle} {p : SolarTV.EVM.Program.layer.Prog}
    {q : Bl.Prog} {scope : SolarTV.Call → Prop} {L : LoopRecord} {E B X M : Nat} (m : Nat)
    (loops : ∀ call, scope call →
      Loops (SolarTV.EVM.Program.block o call p) (0, [], SolarTV.Machine.State.initial call) L E B X M)
    (same : ∀ call, scope call →
      SolarTV.EVM.Program.layer.run o p call (fixedFuel E B X M) = Bl.run o q call m) :
    SolarTV.Stage (SolarTV.EVM.Program.layer.sem o) (Bl.sem o) p q scope :=
  SolarTV.Milestone.W1.stage_of_runs (fixedFuel E B X M) m (ends_fixed loops) same

end Verify.Gas.FixedFuel
