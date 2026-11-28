import SolidCore.Refinement.Solar.Milestone
import SolidCore.Refinement.ComposeSeq

/-!
# The w5 milestone on sequences of calls

\`certifiedAt\` (Milestone.lean) states w5's specification from any storage for one call, through
every stage of solar's pipeline. Each stage is proved from any storage, so the stages lift to
sequences of calls (\`StageSeq.of_anyStorage\`, through \`bytecodeSeq_of_stages_invariant\`), and
\`certifiedSeq\` states it for every finite sequence of calls of \`f\`, from any initial storage:
solar's bytecode finishes every call of the sequence, each call meets \`Verify.W5.postAt\`, and
the storage list each call starts from (\`writeBack []\`: the previous call's list, since \`f\`
writes no slot) reads as exactly the previous call's final storage (\`Carries\`).

\`fullMsgs fns\` is the messages of \`fullScope fns\`: a function of \`fns\` on argument words
below \`2 ^ 256\`, with no value, without the storage the sequence supplies.
-/

namespace SolidCore.Refinement.Abi

/-- Every message of a function of \`fns\` on argument words below \`2 ^ 256\`, with no value: the
calls of \`fullScope fns\`, without their storage. -/
def fullMsgs (fns : List Fn) (m : Msg) : Prop :=
  ∃ fn ∈ fns, ∃ args : List Nat, args.length = fn.params.length ∧ (∀ a ∈ args, a < 2 ^ 256) ∧
    m = { calldata := calldata fn.sel args, callvalue := 0 }

/-- A message of \`fullMsgs fns\` from any storage is a call of \`fullScope fns\`. -/
theorem fullScope_call {fns : List Fn} {m : Msg} (h : fullMsgs fns m) (σ : List (Nat × Nat)) :
    fullScope fns σ (m.call σ) := by
  obtain ⟨fn, hfn, args, hlen, hlt, rfl⟩ := h
  exact ⟨fn, hfn, args, hlen, hlt, rfl⟩

end SolidCore.Refinement.Abi

namespace SolidCore.Refinement.Solar.W1

open SolidCore.Refinement SolidCore.Refinement.Abi

/-- What each call of a sequence of w5 meets: \`Verify.W5.postAt\`, and the next call starts
from exactly its final storage. -/
def postSeq (call : Call) (obs : Observable) : Prop :=
  Verify.W5.postAt call obs ∧ Carries (writeBack []) call obs

/-- A call that keeps its storage is carried exactly by \`writeBack []\`. -/
theorem carries_of_postAt {call : Call} {obs : Observable} (h : Verify.W5.postAt call obs) :
    Carries (writeBack []) call obs := by
  funext slot
  simp only [writeBack, List.map_nil, List.append_nil]
  exact (h.2.2 slot).symm

/-- **The w5 milestone on sequences.** solar's runtime bytecode for w5 finishes every finite
sequence of calls of \`f\` (any argument words, no value) from any initial storage under EthLib,
each call meeting w5's specification from its storage (\`Verify.W5.postAt\`) and leaving exactly
the storage the next call starts from, through every stage of solar's pipeline, each proved from
any storage. -/
theorem certifiedSeq :
    SatisfiesSeq ethLib code (writeBack []) (within (fun _ => True) (fullMsgs Corpus.W5.fns))
      (fun _ _ => True) (Each postSeq (writeBack [])) := by
  obtain ⟨c, hc, hspec⟩ := Verify.W5.satisfiesAt
  exact bytecodeSeq_of_stages_invariant
    (Satisfies.mono hspec fun _ _ _ _ h => ⟨h, carries_of_postAt h⟩) (loweringAt oracle hc)
    ((SolarTV.Milestone.W1.w1_mir_to_evmir oracle).mono fun _ _ => trivial) (stageAt oracle)
    (fun σ _ _ hm => ⟨⟨σ, fullScope_call hm σ⟩, trivial⟩) fun _ _ _ _ _ _ => trivial

/-- The one-call milestone from any storage is \`certifiedSeq\`'s length-1 case:
\`certifiedAt\`'s statement as a statement on sequences of one message
(\`satisfiesSeq_single_iff\`). -/
theorem certifiedAt_single :
    SatisfiesSeq ethLib code (writeBack []) (single Verify.W5.scopeAt) (singlePre Verify.W5.pre)
      (singlePost Verify.W5.postAt) :=
  (satisfiesSeq_single_iff _).mpr certifiedAt

/-- info: 'SolidCore.Refinement.Solar.W1.certifiedSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedSeq

end SolidCore.Refinement.Solar.W1
