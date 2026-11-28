import Verify.Phase3.RecSource.Join

/-!
# RecSum: what the published statement covers (reviewed inputs, no proofs)

The valid calls, allowed statuses, postcondition and gas bound of RecSum's published statement
(`Verify/Phase3/RecSource/Certified.lean` proves it). They are the statement's inputs, so they live
apart from the proof module: the statement imports this module and never the proof.

* `Valid`: `total(a)` with `a ≤ 64` and no value, from any storage: the domain of `total`'s
  `@custom:succeeds-if msg.value == 0 && n <= 64`;
* `Allowed`: success;
* `Post`: `total`'s `@custom:ensures n <= 64 ==> result == n * (n + 1) / 2`, the 32-byte word
  of `a * (a + 1) / 2` (a Lean predicate written for the ensures, not solar-verify's export);
* `gas`: `618800 * (2 * a + 4) + 9`, the assembly checker's bound for `2 * a + 4` blocks.
-/

namespace Verify.Phase3.RecSource.Cert

open SolarTV SolarTV.Machine
open SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.Generic.Loop
open Verify.Phase3.RecSource (totalSel wordOut)

/-- The call of `total(a)` with no value, from storage `σ`. -/
def totalCall (a : Nat) (σ : List (Nat × Nat)) : Call :=
  { calldata := Abi.calldata totalSel [a], callvalue := 0, storage := σ }

/-- The calls the statement covers: `total(a)` with `a ≤ 64` and no value, from any storage. -/
def Valid (call : Call) : Prop := ∃ a σ, a ≤ 64 ∧ call = totalCall a σ

/-- The allowed statuses: success (`total`'s succeeds-if holds on every valid call). -/
def Allowed (_ : Call) (obs : Observable) : Prop := obs.success = true

/-- `total`'s ensures: on `total(a)`, `a ≤ 64`, the result is the word `a * (a + 1) / 2`. -/
def Post (call : Call) (obs : Observable) : Prop :=
  ∀ a σ, call = totalCall a σ → a ≤ 64 → obs.output = wordOut (a * (a + 1) / 2)

/-- The gas bound: the assembly checker's for `2 * a + 4` blocks of the final EVM IR. -/
def gas (call : Call) : Nat := 618800 * (2 * (calldataWord call 4).toNat + 4) + 9

/-- What every valid call returns: success, the word `a * (a + 1) / 2`, no logs, the storage. -/
def result (a : Nat) (σ : List (Nat × Nat)) : Observable :=
  ⟨true, wordOut (a * (a + 1) / 2), [], slotValue σ⟩

/-- The specification and the allowed statuses are not vacuous (the statement's `NonVacuous`). -/
theorem nonvacuous :
    (∃ (call : SolarTV.Call) (obs : SolarTV.Observable), Valid call ∧ ¬ Post call obs) ∧
      (∃ (call : SolarTV.Call) (obs : SolarTV.Observable), Valid call ∧ obs.success = false ∧
        ¬ Allowed call obs) := by
  refine ⟨⟨totalCall 2 [], ⟨true, wordOut (2 * 2), [], slotValue []⟩, ⟨2, [], by decide, rfl⟩, ?_⟩,
    ⟨totalCall 0 [], ⟨false, [], [], slotValue []⟩, ⟨0, [], by decide, rfl⟩, rfl, by simp [Allowed]⟩⟩
  intro h
  have := h 2 [] rfl (by decide)
  revert this
  decide

end Verify.Phase3.RecSource.Cert
