import Verify.SourceText.Tests
import Verify.VC.KernelIdx

/-!
# G0's tests, by run: the body and swap mutations change what the contract does

Each run is SolidCore's `Source.run` of a call, evaluated by the kernel (`kernel_rfl`) with the existing
`Verify.VC.mkIdx_eq`, which rewrites the hash map's `USize` index through `Nat`. No second interpreter,
no storage model of its own; Lean's three axioms only. These are the denotation check of each
run-level mutation: the same call, from the same storage, shows different storage under the
original's and the mutation's reading, so the readings differ.

* LedgerRelay `setPair(1, 2)` from empty storage: original `stamp = 17`, body mutation `18`.
* LedgerRelay `relay(9)` from `right = 7`: original `left = 7` (`old(right)`), the reordered
  assignments `left = 9`.
* Flag `raise(5)`: original `raised = 1`, body mutation `2`.

The property row stays NOT RUN for LedgerRelay: no `Expected` of LedgerRelay is proved, so nothing
here says its run meets or breaks its ensures for every call.
-/

namespace SolidCore.Verify.SourceText

open SolidCore.Solidity

/-- The checked contract of a reading, with fuel `fuel`. -/
def Reading.checkedAt (r : Reading) (fuel : Nat) : Option TypeCheck.CheckedContract :=
  match (r.source fuel).checked with
  | .ok c => some c
  | .error _ => none

end SolidCore.Verify.SourceText

namespace SolidCore.Verify.SourceText.Tests

open SolidCore.Refinement SolidCore.Verify.SourceText SolidCore.Solidity

/-- SolidCore's fuel in the tests' runs. -/
def fuel : Nat := 4096

/-- The selector the reading's own ABI gives a signature. -/
def selOf (r : Reading) (s : String) : Nat := ((r.abi.find? (·.1 == s)).map (·.2.sel)).getD 0

/-- What a run shows: its status and storage slots `0 .. n-1`. -/
def shows (o : Option SolarTV.Observable) (n : Nat) : Option (Bool × List Nat) :=
  o.map fun obs => (obs.success, (List.range n).map obs.storage)

/-- The call: call data for `sel` and `args`, no value, storage `σ`. -/
def callOf (sel : Nat) (args : List Nat) (σ : List (Nat × Nat)) : SolarTV.Call :=
  { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }

/-- What SolidCore's run of a reading's call shows. -/
def direct (r : Reading) (s : String) (args : List Nat) (σ : List (Nat × Nat)) (n : Nat) : Option (Bool × List Nat) :=
  match r.checkedAt fuel with
  | none => none
  | some c => shows (Source.run fuel c (callOf (selOf r s) args σ)) n

/-- Two readings whose runs of one call show differently are different readings. -/
theorem ne_of_runs {r r' : Reading} {s : String} {args : List Nat} {σ : List (Nat × Nat)} {n : Nat}
    (h : direct r s args σ n ≠ direct r' s args σ n) : r ≠ r' := fun he => h (he ▸ rfl)

/-- A shown result is SolidCore's run of the call. -/
theorem run_shows {r : Reading} {s : String} {args : List Nat} {σ : List (Nat × Nat)} {n : Nat}
    {b : Bool} {ws : List Nat} (h : direct r s args σ n = some (b, ws)) :
    ∃ c o, r.checkedAt fuel = some c ∧
      Source.run fuel c (callOf (selOf r s) args σ) = some o ∧
      o.success = b ∧ (List.range n).map o.storage = ws := by
  unfold direct at h
  cases hc : r.checkedAt fuel with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only [] at h
    unfold shows at h
    cases ho : Source.run fuel c (callOf (selOf r s) args σ) with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨c, o, rfl, ho, h.1, h.2⟩

namespace Ledger

open Cases

def origSetPair := direct LedgerRelay.upstream "setPair(uint256,uint256)" [1, 2] [] 3
kernel_rfl origSetPair_eq origSetPair (some (true, [1, 2, 17])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

def bodySetPair := direct LedgerRelayBody.upstream "setPair(uint256,uint256)" [1, 2] [] 3
kernel_rfl bodySetPair_eq bodySetPair (some (true, [1, 2, 18])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

def origRelay := direct LedgerRelay.upstream "relay(uint256)" [9] [(1, 7)] 3
kernel_rfl origRelay_eq origRelay (some (true, [7, 9, 3])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

def swapRelay := direct LedgerRelaySwap.upstream "relay(uint256)" [9] [(1, 7)] 3
kernel_rfl swapRelay_eq swapRelay (some (true, [9, 9, 3])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

/-- The original's `relay(9)` from `right = 7` is SolidCore's run, and leaves `left = 7`. -/
theorem relay_run : ∃ c o, LedgerRelay.upstream.checkedAt fuel = some c ∧
    Source.run fuel c (callOf (selOf LedgerRelay.upstream "relay(uint256)") [9] [(1, 7)]) = some o ∧ o.success = true ∧ (List.range 3).map o.storage = [7, 9, 3] :=
  run_shows origRelay_eq

/-- The reordered relay's run leaves `left = 9`. -/
theorem swap_run : ∃ c o, LedgerRelaySwap.upstream.checkedAt fuel = some c ∧
    Source.run fuel c (callOf (selOf LedgerRelaySwap.upstream "relay(uint256)") [9] [(1, 7)]) = some o ∧ o.success = true ∧ (List.range 3).map o.storage = [9, 9, 3] :=
  run_shows swapRelay_eq

theorem body_rejects : (read LedgerRelayBody.bytes).isSome ∧ read LedgerRelayBody.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [body_agrees]; rfl, ?_⟩
  rw [body_agrees]
  refine fun h => ne_of_runs (s := "setPair(uint256,uint256)") (args := [1, 2]) (σ := []) (n := 3) ?_ (Option.some.inj h)
  show bodySetPair ≠ origSetPair
  rw [bodySetPair_eq, origSetPair_eq]; decide

theorem swap_rejects : (read LedgerRelaySwap.bytes).isSome ∧ read LedgerRelaySwap.bytes ≠ some LedgerRelay.upstream := by
  refine ⟨by rw [swap_agrees]; rfl, ?_⟩
  rw [swap_agrees]
  refine fun h => ne_of_runs (s := "relay(uint256)") (args := [9]) (σ := [(1, 7)]) (n := 3) ?_ (Option.some.inj h)
  show swapRelay ≠ origRelay
  rw [swapRelay_eq, origRelay_eq]; decide

end Ledger

namespace FlagCases

open Cases

def origRaise := direct Flag.upstream "raise(uint256)" [5] [] 2
kernel_rfl origRaise_eq origRaise (some (true, [5, 1])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

def bodyRaise := direct FlagBody.upstream "raise(uint256)" [5] [] 2
kernel_rfl bodyRaise_eq bodyRaise (some (true, [5, 2])) using Cases.Selectors.selector_eq SolidCore.Verify.VC.mkIdx_eq

theorem body_rejects : (read FlagBody.bytes).isSome ∧ read FlagBody.bytes ≠ some Flag.upstream := by
  refine ⟨by rw [body_agrees]; rfl, ?_⟩
  rw [body_agrees]
  refine fun h => ne_of_runs (s := "raise(uint256)") (args := [5]) (σ := []) (n := 2) ?_ (Option.some.inj h)
  show bodyRaise ≠ origRaise
  rw [bodyRaise_eq, origRaise_eq]; decide

end FlagCases

end SolidCore.Verify.SourceText.Tests
