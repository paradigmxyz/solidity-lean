import SolidCore.Refinement.Solar.Counter.Every
import SolidCore.Refinement.ComposeSeq

/-!
# The counter on every sequence of calls

certifiedSeqEvery lifts certifiedEvery (Every.lean) to sequences with ComposeSeq.lean's
bytecodeSeq_of_stages_invariant: solar's bytecode for Counter finishes every finite sequence of
calls of scopeEvery (inc and get, with or without value, malformed call data and unknown
selectors) from any initial storage under EthLib, each call showing expectedEvery from the
storage it starts from and leaving exactly the storage the next call starts from (writeBack of
slot 0, carries_every), through every stage of solar's pipeline.
-/

namespace SolidCore.Refinement.Solar.Counter

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Verify

/-- What each call of a sequence meets: expectedEvery, and the next call starts from exactly its
final storage. -/
def postEverySeq (call : Call) (obs : Observable) : Prop :=
  postEvery call obs ∧ Carries (writeBack [0]) call obs

/-- Every call changes slot 0 at most, so writing slot 0 back carries its final storage. -/
theorem carries_every (call : Call) : Carries (writeBack [0]) call (expectedEvery call) := by
  have base : ∀ obs : Observable, obs.storage = slotValue call.storage →
      Carries (writeBack [0]) call obs := fun obs h =>
    carries_writeBack (fun slot _ => by rw [h])
      (fun slot => by rw [h]; exact (Evm.Wide.slotValue_mod call.storage slot).symm)
      (fun slot => by rw [h]; exact Evm.Wide.slotValue_lt _ _)
  unfold expectedEvery
  split_ifs with h1 h2 h3
  · exact base _ rfl
  · exact base _ rfl
  · unfold expectedAt
    split_ifs with hof
    · refine carries_writeBack (fun slot hne => ?_) (fun slot => ?_) (fun slot => ?_)
      · have hs : ¬ slot % 2 ^ 256 = 0 := fun e =>
          hne 0 List.mem_cons_self (by rw [e, Nat.zero_mod])
        simp only [hs, ↓reduceIte]
      · dsimp only
        rw [Nat.mod_mod, ← Evm.Wide.slotValue_mod call.storage slot]
      · by_cases hs : slot % 2 ^ 256 = 0
        · simp only [hs, ↓reduceIte]
          exact hof
        · simp only [hs, ↓reduceIte]
          exact Evm.Wide.slotValue_lt _ _
    · exact base _ rfl
  · exact base _ rfl

/-- **The counter on every sequence of calls.** solar's runtime bytecode for Counter finishes
every finite sequence of calls of scopeEvery from any initial storage under EthLib, each call
showing expectedEvery from the storage it starts from and leaving exactly the storage the next
call starts from, through every stage of solar's pipeline. -/
theorem certifiedSeqEvery :
    SatisfiesSeq ethLib code (writeBack [0]) (within (fun _ => True) fun m => scopeEvery (m.call []))
      (fun _ _ => True) (Each postEverySeq (writeBack [0])) := by
  obtain ⟨c, hc, hspec⟩ := satisfiesEvery
  exact bytecodeSeq_of_stages_invariant
    (Satisfies.mono hspec fun call _ _ obs h => ⟨h, by rw [h]; exact carries_every call⟩)
    (loweringEvery SolidCore.Refinement.Solar.W1.oracle hc)
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir SolidCore.Refinement.Solar.W1.oracle).mono
      fun _ _ => trivial)
    ((assemblyEvery SolidCore.Refinement.Solar.W1.oracle).mono fun _ h => h.1)
    (fun _ _ _ hm => ⟨hm, trivial⟩) fun _ _ _ _ _ _ => trivial

/-- info: 'SolidCore.Refinement.Solar.Counter.certifiedSeqEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certifiedSeqEvery

end SolidCore.Refinement.Solar.Counter
