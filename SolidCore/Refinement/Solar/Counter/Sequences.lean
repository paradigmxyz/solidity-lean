import SolidCore.Refinement.Solar.Counter.Milestone
import SolidCore.Refinement.Solar.Sequences

/-!
# The counter milestone on sequences of calls

`certifiedAt` (Milestone.lean, from SpecAt.lean, LoweringAt.lean and AssemblyAt.lean) proves Counter's `inc` through every stage of solar's pipeline
from any storage, and every stage is proved from any storage, so the milestone lifts to every
finite sequence of calls (`bytecodeSeq_of_stages_invariant`, ComposeSeq.lean). Each call starts from
the storage the previous one left: the carry is `writeBack [0]`, the previous call's storage list with
slot 0 overwritten by its final word, which reads back as exactly the previous call's final
storage because `inc` changes no other slot (`carries_of_post`).

* `certifiedSeq`: from any initial storage, solar's bytecode finishes every sequence of calls of
  `inc` (any argument words below `2 ^ 256`, no value) under EthLib, and every call meets `post`
  from the storage it starts from and leaves exactly the storage the next call starts from.
* `certifiedAt_single`: its one-call case is `certifiedAt` (`satisfiesSeq_single_iff`).
* `total`: a consequence on the bytecode itself: from any storage whose slot 0 holds `x`, the
  calls `inc(d₁) … inc(dₙ)` all succeed when `x + d₁ + … + dₙ` fits in 256 bits, and the last
  leaves slot 0 holding that sum.
-/

namespace SolidCore.Refinement.Solar.Counter

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Verify

/-- What each call of a sequence of `inc` meets: `post`, and the next call starts from exactly its
final storage. -/
def postSeq (call : Call) (obs : Observable) : Prop :=
  post call obs ∧ Carries (writeBack [0]) call obs

/-- The final storage `post` describes, slot by slot: slot 0 holds `x + d` when it fits, and every
other slot, or every slot on overflow, is the call's. -/
theorem storage_of_post {call : Call} {obs : Observable} (h : post call obs) (slot : Nat) :
    obs.storage slot =
      if slotValue call.storage 0 + (argWords 1 call).getD 0 0 < 2 ^ 256 ∧ slot % 2 ^ 256 = 0 then
        slotValue call.storage 0 + (argWords 1 call).getD 0 0
      else slotValue call.storage slot := by
  simp only [post] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i hf
    rw [h.2.2 slot]
    by_cases hs : slot % 2 ^ 256 = 0
    · simp only [hs, hf, and_self, ↓reduceIte]
    · simp only [hs, and_false, ↓reduceIte]
  · rename_i hf
    rw [h.2.2 slot]
    simp only [hf, false_and, ↓reduceIte]

/-- A call that meets `post` is carried exactly by `writeBack [0]`: it changes slot 0 only. -/
theorem carries_of_post {call : Call} {obs : Observable} (h : post call obs) :
    Carries (writeBack [0]) call obs := by
  refine carries_writeBack (fun slot hne => ?_) (fun slot => ?_) (fun slot => ?_)
  · have hs : ¬ slot % 2 ^ 256 = 0 := fun e =>
      hne 0 List.mem_cons_self (by rw [e, Nat.zero_mod])
    rw [storage_of_post h slot]
    simp only [hs, and_false, ↓reduceIte]
  · rw [storage_of_post h slot, storage_of_post h (slot % 2 ^ 256), Nat.mod_mod,
    Evm.Wide.slotValue_mod call.storage slot]
  · rw [storage_of_post h slot]
    split
    · rename_i hc
      exact hc.1
    · exact Evm.Wide.slotValue_lt _ _

/-- **The counter milestone on sequences.** solar's runtime bytecode for Counter finishes every
finite sequence of calls of `inc` (any argument words, no value) from any initial storage under
EthLib, each call meeting `inc`'s specification (`post`) from the storage it starts from and leaving
exactly the storage the next call starts from, through every stage of solar's pipeline, each
proved from any storage. -/
theorem certifiedSeq :
    SatisfiesSeq ethLib code (writeBack [0]) (within (fun _ => True) (fullMsgs fns))
      (fun _ _ => True) (Each postSeq (writeBack [0])) := by
  obtain ⟨c, hc, hspec⟩ := satisfiesAt
  exact bytecodeSeq_of_stages_invariant
    (Satisfies.mono hspec fun _ _ _ _ h => ⟨h, carries_of_post h⟩) (loweringAt W1.oracle hc)
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir W1.oracle).mono fun _ _ => trivial)
    (stageAt W1.oracle) (fun σ _ _ hm => ⟨⟨σ, fullScope_call hm σ⟩, trivial⟩)
    fun _ _ _ _ _ _ => trivial

/-- The one-call milestone from any storage is `certifiedSeq`'s length-1 case: `certifiedAt`'s
statement on the sequences of one message (`satisfiesSeq_single_iff`). -/
theorem certifiedAt_single :
    SatisfiesSeq ethLib code (writeBack [0]) (single scopeAt) (singlePre pre) (singlePost post) :=
  (satisfiesSeq_single_iff _).mpr certifiedAt.2.2.2

/-! ## The total -/

/-- The message of `inc(d)`, with no value. -/
def incMsgOf (d : Nat) : Msg := { calldata := calldata incSelector [d], callvalue := 0 }

theorem fullMsgs_incMsgOf {d : Nat} (hd : d < 2 ^ 256) : fullMsgs fns (incMsgOf d) :=
  ⟨_, List.mem_singleton_self _, [d], rfl, by simpa using hd, rfl⟩

theorem argWords_incMsgOf {d : Nat} (hd : d < 2 ^ 256) (σ : List (Nat × Nat)) :
    argWords 1 ((incMsgOf d).call σ) = [d] :=
  Verify.argWords_calldata incSelector [d] (by simpa using hd) 0 σ

/-- Along a run that meets `postSeq` on every call, the calls `inc(d₁) … inc(dₙ)` from a storage whose
slot 0 holds `x` all succeed when `x + d₁ + … + dₙ` fits, and the last leaves slot 0 holding it. -/
theorem total_of_each :
    ∀ (ds : List Nat) (σ : List (Nat × Nat)) (obss : List Observable),
      Each postSeq (writeBack [0]) σ (ds.map incMsgOf) obss → (∀ d ∈ ds, d < 2 ^ 256) →
      slotValue σ 0 + ds.sum < 2 ^ 256 →
      (∀ obs ∈ obss, obs.success = true) ∧
        ∀ obs ∈ obss.getLast?, obs.storage 0 = slotValue σ 0 + ds.sum
  | [], _, [], _, _, _ => ⟨by simp, by simp⟩
  | d :: ds, σ, obs :: os, ⟨⟨hpost, hcarry⟩, hrest⟩, hds, hsum => by
    have hd : d < 2 ^ 256 := hds d List.mem_cons_self
    have hw := argWords_incMsgOf hd σ
    have hcall : ((incMsgOf d).call σ).storage = σ := rfl
    have hfit : slotValue σ 0 + d < 2 ^ 256 := by simp only [List.sum_cons] at hsum; omega
    have hpost' := hpost
    simp only [post, hw, hcall, List.getD_cons_zero, hfit, ↓reduceIte] at hpost'
    have h0 : obs.storage 0 = slotValue σ 0 + d := by
      rw [hpost'.2.2.2 0]
      simp
    have hσ : slotValue (writeBack [0] ((incMsgOf d).call σ) obs) 0 = slotValue σ 0 + d := by
      rw [hcarry, h0]
    obtain ⟨hs, hl⟩ := total_of_each ds _ os hrest (fun d' h' => hds d' (List.mem_cons_of_mem _ h'))
      (by rw [hσ]; simp only [List.sum_cons] at hsum; omega)
    refine ⟨?_, ?_⟩
    · intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hpost'.2.1
      · exact hs o ho
    · intro o ho
      cases os with
      | nil =>
        cases ds with
        | nil =>
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ho
          subst ho
          simp [h0]
        | cons _ _ => exact hrest.elim
      | cons o' os' =>
        rw [List.getLast?_cons_cons] at ho
        rw [hl o ho, hσ, List.sum_cons]
        omega

/-- **The total.** From any storage `σ` whose slot 0 holds `x`, solar's bytecode for Counter runs the
calls `inc(d₁) … inc(dₙ)` one after the other under EthLib, each from the storage the previous one
left, and when `x + d₁ + … + dₙ` fits in 256 bits every call succeeds and the last leaves slot 0
holding that sum. -/
theorem total (ds : List Nat) (σ : List (Nat × Nat)) (hds : ∀ d ∈ ds, d < 2 ^ 256)
    (hsum : slotValue σ 0 + ds.sum < 2 ^ 256) :
    ∃ obss, seqRun ethLib code (writeBack [0]) σ (ds.map incMsgOf) = some obss ∧
      (∀ obs ∈ obss, obs.success = true) ∧
      ∀ obs ∈ obss.getLast?, obs.storage 0 = slotValue σ 0 + ds.sum := by
  obtain ⟨obss, hrun, heach⟩ := certifiedSeq σ (ds.map incMsgOf)
    ⟨trivial, fun m hm => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      exact fullMsgs_incMsgOf (hds d hd)⟩ trivial
  exact ⟨obss, hrun, total_of_each ds σ obss heach hds hsum⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.certifiedSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedSeq

/-- info: 'SolidCore.Refinement.Solar.Counter.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms total

end SolidCore.Refinement.Solar.Counter



