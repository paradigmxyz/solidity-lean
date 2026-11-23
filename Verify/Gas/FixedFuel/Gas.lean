import Verify.Gas.FixedFuel.Run
import SolidCore.Refinement.Solar.AssembleGasLoop
import Verify.Shapes
import Mathlib.Tactic.Ring

/-!
# Fixed-fuel gas for a loop: a per-iteration bound and the resource obligation

The loop checker's forward theorem (`forward_of_checkL`, `stage_of_checkL_gas`) gives the
bytecode the EVM IR's result at every gas from `gasBoundL c n` on, where `n` is a block fuel at
which the EVM IR ends. `gasBoundL c n` is linear in `n`, so the fuel of `Run.lean` splits it
into a per-iteration part and an exit part:

    gasBoundL c (E + n * B + X) = n * perIterGas c B + exitGas c E X

(`gasBoundL_eq`). The gas lemma (`gas_of_steps`) takes the record's own chain
`LoopRecord.Steps L n σ` as its premise and bounds that by `fixedGas c E B X M`, the bound at
the measure bound `M`. With a bridge for every call in scope, `fixedGas` is a gas bound in the
sense of `Shapes.Resources` (`forward_of_loops`, `resources_of_loops`).

## Three outcomes, kept apart

`verdictOf` is the resource verdict the driver emits:
* `bounded G`: the fixed bound is below `2 ^ 64` and is the obligation's `G`;
  `resources_of_verdict` turns it, with the bridges, into `Shapes.Resources`.
* `outOfGas G`: the fixed bound is at least `2 ^ 64`. No `Resources` holds at it
  (`not_resources_of_outOfGas`); the run is REJECTED for resources, nothing else.
* `unsupported`: no measure bound (the loop is outside the counted shape); nothing is claimed.

A revert is none of these: it is a result. `forward_of_loops` gives the bytecode the EVM IR's
result whatever it is, so a reverting run at a bounded `G` is the source's revert, exactly
(`revert_of_loops`).
-/

namespace Verify.Gas.FixedFuel

open SolidCore.Refinement.Solar.Assemble SolarTV.Assembly
open SolidCore.Refinement.Solar.AssembleLoop
open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open Verify.LoopSource.Interface
open SolidCore.Refinement.Generic (Val)

/-- The loop checker's gas for one iteration of at most `B` blocks. -/
def perIterGas (c : Cert) (B : Nat) : Nat := 22100 * (B * bmax c)

/-- The loop checker's gas for the blocks outside the iterations, and memory. -/
def exitGas (c : Cert) (E X : Nat) : Nat := 22100 * ((E + X) * bmax c) + memoryGasCost c.top

/-- **The fixed gas bound**: `M` iterations and the exit. -/
def fixedGas (c : Cert) (E B X M : Nat) : Nat := M * perIterGas c B + exitGas c E X

/-- **The loop checker's bound splits per iteration.** -/
theorem gasBoundL_eq (c : Cert) (E B X n : Nat) :
    gasBoundL c (E + n * B + X) = n * perIterGas c B + exitGas c E X := by
  unfold gasBoundL perIterGas exitGas
  ring

theorem gasBoundL_fixed (c : Cert) (E B X M : Nat) :
    gasBoundL c (fixedFuel E B X M) = fixedGas c E B X M :=
  gasBoundL_eq c E B X M

/-- **The gas lemma**: a run of the record's `n` steps needs the loop checker's gas at its block
fuel, which is `n` times the per-iteration gas plus the exit cost, and at most the fixed bound
at a measure bound `M` of the entry valuation. -/
theorem gas_of_steps {L : LoopRecord} {n : Nat} {σ : Val} (hs : L.Steps n σ) (c : Cert)
    (E B X : Nat) {M : Nat} (hM : L.m σ ≤ M) :
    gasBoundL c (E + n * B + X) = n * perIterGas c B + exitGas c E X ∧
      n * perIterGas c B + exitGas c E X ≤ fixedGas c E B X M := by
  refine ⟨gasBoundL_eq c E B X n, ?_⟩
  have hle : n ≤ M := Nat.le_trans (LoopRecord.steps_le hs) hM
  unfold fixedGas
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hle) _

/-- **The forward theorem at the fixed bound**: with a bridge for the call's loop, the bytecode
gives the EVM IR's result at every gas from `fixedGas` on. -/
theorem forward_of_loops {p : SolidCore.Refinement.Solar.Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) {L : LoopRecord} {E B X M : Nat}
    (loops : Loops (SolarTV.EVM.Program.block o call p)
      (0, [], SolarTV.Machine.State.initial call) L E B X M)
    {gas : Nat} (hg : fixedGas c E B X M ≤ gas) (obs : SolarTV.Observable)
    (hrun : (SolarTV.evmirSem o).run p call = some obs) :
    SolidCore.Refinement.Final.Target.runWith gas code call = some obs :=
  stage_of_checkL_gas hc o ho he call (fixedFuel E B X M) (ends_of_loops loops)
    (by rw [gasBoundL_fixed]; exact hg) obs hrun

/-- **A revert is a result, not a resource verdict**: at the fixed bound the bytecode reverts
exactly when the EVM IR does, with its data. -/
theorem revert_of_loops {p : SolidCore.Refinement.Solar.Assemble.Program} {code : ByteArray} {c : Cert} {mx : List Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o) (call : SolarTV.Call) {L : LoopRecord} {E B X M : Nat}
    (loops : Loops (SolarTV.EVM.Program.block o call p)
      (0, [], SolarTV.Machine.State.initial call) L E B X M)
    {gas : Nat} (hg : fixedGas c E B X M ≤ gas) (obs : SolarTV.Observable)
    (hrun : (SolarTV.evmirSem o).run p call = some obs) (hf : obs.success = false) :
    ∃ obs', SolidCore.Refinement.Final.Target.runWith gas code call = some obs' ∧
      obs'.success = false ∧ obs'.output = obs.output :=
  ⟨obs, forward_of_loops hc o ho he call loops hg obs hrun, hf, rfl⟩

/-- **The resource obligation from the bridges**: `fixedGas` is a `Shapes.Resources` bound for
every source semantics that stages to the loop's EVM IR. -/
theorem resources_of_loops {S : SolarTV.Sem} {ps : S.Prog} {p : SolidCore.Refinement.Solar.Assemble.Program}
    {code : ByteArray} {c : Cert} {mx : List Nat} {Valid : SolarTV.Call → Prop}
    {L : LoopRecord} {E B X M : Nat}
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o)
    (total : ∀ call, Valid call → ∃ obs, S.run ps call = some obs)
    (stage : SolarTV.Stage S (SolarTV.evmirSem o) ps p Valid)
    (loops : ∀ call, Valid call → Loops (SolarTV.EVM.Program.block o call p)
      (0, [], SolarTV.Machine.State.initial call) L E B X M)
    (hG : fixedGas c E B X M < 2 ^ 64) :
    SolidCore.Refinement.Shapes.Resources S ps code Valid (fun _ => fixedGas c E B X M) :=
  SolidCore.Refinement.Shapes.resources_of_forward total stage fun call hv =>
    ⟨hG, fun _ hg _ obs hrun => forward_of_loops hc o ho he call (loops call hv) hg obs hrun⟩

/-! ## The resource verdict -/

/-- **The resource verdict**: a bound, out of gas, or unsupported, never confused. -/
inductive Verdict where
  | bounded (G : Nat)
  | outOfGas (G : Nat)
  | unsupported
  deriving DecidableEq, Repr

/-- The verdict from a measure bound (`none` when the loop has none), the per-iteration gas and
the exit cost. -/
def verdictOf : Option Nat → Nat → Nat → Verdict
  | none, _, _ => .unsupported
  | some M, pi, ex => if M * pi + ex < 2 ^ 64 then .bounded (M * pi + ex) else .outOfGas (M * pi + ex)

theorem verdictOf_bounded {b : Option Nat} {pi ex G : Nat} (h : verdictOf b pi ex = .bounded G) :
    ∃ M, b = some M ∧ G = M * pi + ex ∧ G < 2 ^ 64 := by
  cases b with
  | none => cases h
  | some M =>
    simp only [verdictOf] at h
    split at h
    · rename_i hl
      cases h
      exact ⟨M, rfl, rfl, hl⟩
    · cases h

theorem verdictOf_outOfGas {b : Option Nat} {pi ex G : Nat} (h : verdictOf b pi ex = .outOfGas G) :
    ∃ M, b = some M ∧ G = M * pi + ex ∧ 2 ^ 64 ≤ G := by
  cases b with
  | none => cases h
  | some M =>
    simp only [verdictOf] at h
    split at h
    · cases h
    · rename_i hl
      cases h
      exact ⟨M, rfl, rfl, Nat.le_of_not_lt hl⟩

/-- **Out of gas refutes the obligation**: no `Resources` holds at an `outOfGas` bound. -/
theorem not_resources_of_outOfGas {b : Option Nat} {pi ex G : Nat}
    (h : verdictOf b pi ex = .outOfGas G) {S : SolarTV.Sem} {p : S.Prog} {code : ByteArray}
    {Valid : SolarTV.Call → Prop} {call : SolarTV.Call} (hc : Valid call) :
    ¬SolidCore.Refinement.Shapes.Resources S p code Valid (fun _ => G) := by
  obtain ⟨_, _, _, hG⟩ := verdictOf_outOfGas h
  exact SolidCore.Refinement.Shapes.not_resources_of_bound hc hG

/-- **A bounded verdict discharges the obligation**, with the bridges. -/
theorem resources_of_verdict {S : SolarTV.Sem} {ps : S.Prog} {p : SolidCore.Refinement.Solar.Assemble.Program}
    {code : ByteArray} {c : Cert} {mx : List Nat} {Valid : SolarTV.Call → Prop}
    {L : LoopRecord} {E B X M G : Nat}
    (hv : verdictOf (some M) (perIterGas c B) (exitGas c E X) = .bounded G)
    (hc : checkL p code c mx = true) (o : SolarTV.Machine.Oracle) (ho : c.env = true → OracleOk o)
    (he : c.reads = true → EnvOk o)
    (total : ∀ call, Valid call → ∃ obs, S.run ps call = some obs)
    (stage : SolarTV.Stage S (SolarTV.evmirSem o) ps p Valid)
    (loops : ∀ call, Valid call → Loops (SolarTV.EVM.Program.block o call p)
      (0, [], SolarTV.Machine.State.initial call) L E B X M) :
    SolidCore.Refinement.Shapes.Resources S ps code Valid (fun _ => G) := by
  obtain ⟨M', hM, hG, hlt⟩ := verdictOf_bounded hv
  cases hM
  subst hG
  exact resources_of_loops hc o ho he total stage loops hlt

end Verify.Gas.FixedFuel
