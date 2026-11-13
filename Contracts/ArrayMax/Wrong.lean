import Contracts.ArrayMax.Entry

/-!
# ArrayMaxEntry.max: a wrong spec fails on a concrete call

`demo` is `max([1, 7, 3])`, ABI-encoded. The kernel runs solar's first lowered MIR on it to the
return of 7 (`demo_halt`), which meets `Post` and refutes the mutant spec "returns the first
element" (`wrong_fails`), by a mismatch of the returned word.
-/

namespace SolarTV.Milestone.ArrayMaxEntry

open Machine SolarTV.Export.ArrayMaxEntry

/-- The 32 big-endian bytes of a number. -/
def word32 (n : Nat) : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (n / 256 ^ (31 - i) % 256)

/-- `max([1, 7, 3])`, ABI-encoded, with no value. -/
def demo : Call :=
  { calldata := ⟨([0x3b, 0xf6, 0xde, 0x96] ++ word32 32 ++ word32 3 ++ word32 1 ++ word32 7 ++
      word32 3).toArray⟩,
    callvalue := 0, storage := [] }

/-- An oracle; the run reads none of it. -/
def demoOracle : Oracle := ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩

theorem demo_isMax : IsMax demo := by unfold IsMax; decide +kernel

theorem demo_fits : CalldataFits demo := by unfold CalldataFits; decide +kernel

theorem demo_len : len demo = 3 := by decide +kernel

theorem demo_elem0 : elem demo 0 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's run of stage0 on `demo`: it returns the word 7. -/
theorem demo_halt : (MIR.Lowered.Module.run demoOracle stage0 demo 40).map Prod.fst =
    some (.ret (Mem.wordBytes 7)) := by
  rfl

/-- The mutant spec: a successful end returns the array's first element. -/
def PostFirst (call : Call) (r : Halt × State) : Prop :=
  (r.1 = .stop ∨ ∃ d, r.1 = .ret d) → r.1 = .ret (Mem.wordBytes (elem call 0))

theorem wordBytes_ne : Mem.wordBytes (7 : W) ≠ Mem.wordBytes (1 : W) := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The mutant spec does not hold of stage0**: `demo`'s end returns 7, not its first element. -/
theorem wrong_fails :
    ¬∀ r, MIR.Lowered.moduleLayer.Ends demoOracle stage0 demo r → PostFirst demo r := by
  intro h
  obtain ⟨r, hr, h1⟩ := Option.map_eq_some_iff.1 demo_halt
  have := h r ⟨40, hr⟩ (Or.inr ⟨_, h1⟩)
  rw [h1] at this
  have e := Halt.ret.inj this
  rw [demo_elem0] at e
  exact wordBytes_ne e

/-- The true spec holds of that end. -/
theorem demo_post : ∀ r, MIR.Lowered.moduleLayer.Ends demoOracle stage0 demo r → Post demo r :=
  fun r e => stage0_post demoOracle demo demo_isMax demo_fits r e

/-- info: 'SolarTV.Milestone.ArrayMaxEntry.wrong_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wrong_fails

/-- info: 'SolarTV.Milestone.ArrayMaxEntry.demo_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms demo_post

end SolarTV.Milestone.ArrayMaxEntry
