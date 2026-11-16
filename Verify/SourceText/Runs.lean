import Verify.SourceText.Tests

/-!
# G0's tests, by run: the body and swap mutations change what the contract does

SolidCore's storage is a `Std.HashMap` indexed through `USize`, whose width
(`System.Platform.numBits`) the kernel cannot reduce, so a run's storage is not kernel-evaluable.
These checks are by compiled evaluation (`native_decide`): beside Lean's axioms each rests on its own
`<theorem>._native.native_decide.ax_*` axiom, the compiled evaluator's answer (`check.sh` prints them
and allows them nowhere else). They are
the denotation check of each run-level mutation: the same calls, from the same pre-state, show
different storage under the original's and the mutation's reading, so the readings differ.

* LedgerRelay `setPair(1, 2)` from empty storage: original `stamp = 17`, body mutation `18`.
* LedgerRelay `relay(9)` from `right = 7`: original `left = 7` (`old(right)`), the reordered
  assignments `left = 9`.
* Flag `raise(5)`: original `raised = 1`, body mutation `2`.

The property row stays NOT RUN for LedgerRelay: the spec evaluator is noncomputable, and no
certificate of LedgerRelay exists to give `HoldsFn`.
-/

namespace SolidCore.Verify.SourceText.Tests

open SolidCore.Refinement SolidCore.Refinement.Shapes SolidCore.Verify.SourceText
open SolarTV

/-- SolidCore's fuel in the tests' runs. -/
def fuel : Nat := 4096

/-- The checked contract of a reading. -/
def checked (r : Reading) : Option SolidCore.Solidity.TypeCheck.CheckedContract :=
  match (r.source fuel).checked with
  | .ok c => some c
  | .error _ => none

/-- The call to the reading's ABI function with signature `s`, argument words and storage. -/
def callTo (r : Reading) (s : String) (args : List Nat) (storage : List (Nat × Nat)) : Option Call :=
  (r.abi.find? (·.1 == s)).map fun e => { calldata := Abi.calldata e.2.sel args, callvalue := 0, storage }

/-- SolidCore's run of that call. -/
def runOn (r : Reading) (s : String) (args : List Nat) (storage : List (Nat × Nat)) : Option Observable := do
  let c ← checked r
  let call ← callTo r s args storage
  Source.run fuel c call

/-- What a run shows: its status and storage slots `0 .. n-1`. -/
def shows (o : Option Observable) (n : Nat) : Option (Bool × List Nat) :=
  o.map fun obs => (obs.success, (List.range n).map obs.storage)

namespace Ledger

open Cases

/-! ### Runs: `setPair(1, 2)` from empty storage, `relay(9)` from `right = 7` -/

def origSetPair := shows (runOn LedgerRelay.upstream "setPair(uint256,uint256)" [1, 2] []) 3
theorem origSetPair_eq : origSetPair = (some (true, [1, 2, 17])) := by native_decide

def bodySetPair := shows (runOn LedgerRelayBody.upstream "setPair(uint256,uint256)" [1, 2] []) 3
theorem bodySetPair_eq : bodySetPair = (some (true, [1, 2, 18])) := by native_decide

def origRelay := shows (runOn LedgerRelay.upstream "relay(uint256)" [9] [(1, 7)]) 3
theorem origRelay_eq : origRelay = (some (true, [7, 9, 3])) := by native_decide

def swapRelay := shows (runOn LedgerRelaySwap.upstream "relay(uint256)" [9] [(1, 7)]) 3
theorem swapRelay_eq : swapRelay = (some (true, [9, 9, 3])) := by native_decide

theorem body_rejects : (read LedgerRelayBody.bytes).isSome ∧ read LedgerRelayBody.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [body_agrees]; rfl, fun h => ?_⟩
  rw [body_agrees] at h
  have := bodySetPair_eq
  unfold bodySetPair at this
  rw [Option.some.inj h, ← origSetPair.eq_def, origSetPair_eq] at this
  simp at this

theorem swap_rejects : (read LedgerRelaySwap.bytes).isSome ∧ read LedgerRelaySwap.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [swap_agrees]; rfl, fun h => ?_⟩
  rw [swap_agrees] at h
  have := swapRelay_eq
  unfold swapRelay at this
  rw [Option.some.inj h, ← origRelay.eq_def, origRelay_eq] at this
  simp at this

end Ledger

namespace FlagCases

open Cases

def origRaise := shows (runOn Flag.upstream "raise(uint256)" [5] []) 2
theorem origRaise_eq : origRaise = (some (true, [5, 1])) := by native_decide

def bodyRaise := shows (runOn FlagBody.upstream "raise(uint256)" [5] []) 2
theorem bodyRaise_eq : bodyRaise = (some (true, [5, 2])) := by native_decide

theorem body_rejects : (read FlagBody.bytes).isSome ∧ read FlagBody.bytes ≠ some Flag.upstream := by
  refine ⟨by rw [body_agrees]; rfl, fun h => ?_⟩
  rw [body_agrees] at h
  have := bodyRaise_eq
  unfold bodyRaise at this
  rw [Option.some.inj h, ← origRaise.eq_def, origRaise_eq] at this
  simp at this

end FlagCases

end SolidCore.Verify.SourceText.Tests
