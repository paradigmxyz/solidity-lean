import SolidCore.Refinement.Spec
import SolidCore.Refinement.Sequence

/-!
# Composing refinements across compiler stages, for sequences of calls

\`Compose.lean\` relates one call: a \`Stage A B p q scope\` says that on every call of \`scope\`
on which \`p\` finishes, \`q\` finishes with the same observable. A deployed contract sees a
sequence of calls, each starting from the storage the previous one left. This module lifts
the single-call interface to sequences, additively: nothing of \`Compose.lean\`, \`Spec.lean\`
or SolarTV's \`Sem\` changes.

## Carrying storage

A \`Call\` takes its initial storage as a list of (slot, value) pairs, while
\`Observable.storage\` is a function of every slot. A sequence therefore runs with a
\`Carry\`: the list the next call starts from, given the call before it and what it
showed. \`runCalls\` runs a list of messages (\`Msg\`: call data and value) from an initial
storage list, giving the list of observables, or \`none\` when any call does not finish.
\`seqRun S p\` is that run in the language \`S\`. \`Carries carry call obs\` says the carried
list reads back, slot by slot through \`slotValue\`, as exactly the final storage of \`obs\`,
so the next call starts from the previous call's final storage. \`writeBack W\` carries the
previous call's list with the slots \`W\` overwritten by their final values, which is exact
for a call that changes only slots of \`W\` (\`carries_writeBack\`).

## Stages, specifications and refinement of sequences

A sequence scope is a predicate on the initial storage and the messages.

* \`StageSeq A B p q carry scope\`: on every sequence of \`scope\` that \`p\` finishes, \`q\`
  finishes with the same observables. \`StageSeq.trans\` composes stages.
* \`StageSeq.of_stage\`: a single-call stage holds on every sequence whose calls stay in its
  scope (\`Along\`), so \`StageSeq.of_invariant\` lifts a stage to the sequences from a set of
  storages \`St\` of messages of \`M\` when \`St\` is closed under the calls (every storage
  a call from \`St\` produces is in \`St\`), and \`StageSeq.of_anyStorage\` lifts a stage
  proved from any storage to every sequence.
* \`SatisfiesSeq\` is the sequence form of \`Satisfies\`, \`RefinesSeqOn\` the sequence form
  of \`Refines\`; \`bytecodeSeq_of_refines\` and \`bytecodeSeq_of_stages\` carry a sequence
  specification from SolidCore to bytecode, as \`bytecode_of_refines\` and
  \`bytecode_of_stages\` do for one call. \`bytecodeSeq_of_stages_invariant\` is the form the
  milestones use: single-call stages, a single-call specification and a storage set
  closed under that specification give, on bytecode, every call of every sequence meeting
  the specification (\`Each\`).
* Length 1: \`stageSeq_single_iff\`, \`satisfiesSeq_single_iff\` and
  \`refinesSeqOn_single_iff\` recover \`Stage\`, \`Satisfies\` and \`Refines\` as the
  sequences of one message (\`single\`).
* \`refinesSeqOn_of_refinesSeq\` and \`refinesSeq_of_refinesSeqOn\` relate \`RefinesSeqOn\`
  to \`Sequence.lean\`'s \`RefinesSeq\`, whose carried list depends on the observable only.
-/

namespace SolidCore.Refinement

/-! ## Runs of sequences -/

/-- How a sequence carries storage from one call to the next: the storage list the next call
starts from, given the call before it and what that call showed. -/
abbrev Carry := Call → Observable → List (Nat × Nat)

/-- Run the messages \`ms\` one after the other with \`run\`, the first from \`σ\` and each later
one from the storage \`carry\` gives for the call before it. \`none\` when any run is \`none\`. -/
def runCalls (run : Call → Option Observable) (carry : Carry) :
    List (Nat × Nat) → List Msg → Option (List Observable)
  | _, [] => some []
  | σ, m :: ms =>
    match run (m.call σ) with
    | some obs => (runCalls run carry (carry (m.call σ) obs) ms).map (obs :: ·)
    | none => none

/-- The run of the messages \`ms\` from \`σ\` with the program \`p\` of the language \`S\`. -/
def seqRun (S : Sem) (p : S.Prog) (carry : Carry) (σ : List (Nat × Nat)) (ms : List Msg) :
    Option (List Observable) :=
  runCalls (S.run p) carry σ ms

/-- A sequence of messages finishes as its first call and the rest from its carried storage
do. -/
theorem runCalls_cons_eq_some {run : Call → Option Observable} {carry : Carry}
    {σ : List (Nat × Nat)} {m : Msg} {ms : List Msg} {obss : List Observable} :
    runCalls run carry σ (m :: ms) = some obss ↔
      ∃ obs os, run (m.call σ) = some obs ∧
        runCalls run carry (carry (m.call σ) obs) ms = some os ∧ obss = obs :: os := by
  simp only [runCalls]
  cases h : run (m.call σ) with
  | none => simp
  | some obs =>
    simp only [Option.map_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨os, hos, rfl⟩
      exact ⟨obs, os, rfl, hos, rfl⟩
    · rintro ⟨_, os, rfl, hos, rfl⟩
      exact ⟨os, hos, rfl⟩

/-- A sequence of one message runs as its call. -/
theorem runCalls_singleton (run : Call → Option Observable) (carry : Carry)
    (σ : List (Nat × Nat)) (m : Msg) :
    runCalls run carry σ [m] = (run (m.call σ)).map ([·]) := by
  simp only [runCalls]
  cases run (m.call σ) <;> rfl

/-- A run carries one observable for each message. -/
theorem length_of_runCalls {run : Call → Option Observable} {carry : Carry} :
    ∀ {σ : List (Nat × Nat)} {ms : List Msg} {obss : List Observable},
      runCalls run carry σ ms = some obss → obss.length = ms.length
  | _, [], _, h => by cases h; rfl
  | _, _ :: _, _, h => by
    obtain ⟨_, _, _, hos, rfl⟩ := runCalls_cons_eq_some.mp h
    simp [length_of_runCalls hos]

/-- The message of \`call\`: its call data and value, without its storage. -/
def Msg.of (call : Call) : Msg := { calldata := call.calldata, callvalue := call.callvalue }

/-- Every call is its message from its storage. -/
theorem Msg.of_call (call : Call) : (Msg.of call).call call.storage = call := by
  cases call
  rfl

/-! ## Carried storage -/

/-- The storage list \`carry\` gives after \`call\` reads as exactly the final storage of \`obs\`. -/
def Carries (carry : Carry) (call : Call) (obs : Observable) : Prop :=
  slotValue (carry call obs) = obs.storage

/-- Carry the previous call's storage list with the slots \`W\` overwritten by their final
values. -/
def writeBack (W : List Nat) : Carry :=
  fun call obs => call.storage ++ W.map fun k => (k, obs.storage k)

/-- A pair appended to a storage list wins for its slot. -/
theorem slotValue_append_pair (σ : List (Nat × Nat)) (k v slot : Nat) :
    slotValue (σ ++ [(k, v)]) slot =
      if k % 2 ^ 256 = slot % 2 ^ 256 then v % 2 ^ 256 else slotValue σ slot := by
  simp [slotValue, List.foldl_append]

/-- \`writeBack W\` carries exactly the final storage of a call that keeps every slot outside
\`W\` (modulo \`2 ^ 256\`), whose final storage gives the same word for slots equal modulo
\`2 ^ 256\` and holds words below \`2 ^ 256\`. -/
theorem carries_writeBack {W : List Nat} {call : Call} {obs : Observable}
    (hkeep : ∀ slot, (∀ k ∈ W, k % 2 ^ 256 ≠ slot % 2 ^ 256) →
      obs.storage slot = slotValue call.storage slot)
    (hmod : ∀ slot, obs.storage slot = obs.storage (slot % 2 ^ 256))
    (hlt : ∀ slot, obs.storage slot < 2 ^ 256) :
    Carries (writeBack W) call obs := by
  have key : ∀ (V : List Nat) (σ : List (Nat × Nat)) (slot : Nat),
      slotValue (σ ++ V.map fun k => (k, obs.storage k)) slot =
        if ∃ k ∈ V, k % 2 ^ 256 = slot % 2 ^ 256 then obs.storage slot else slotValue σ slot := by
    intro V
    induction V with
    | nil => intro σ slot; simp
    | cons k V ih =>
      intro σ slot
      rw [List.map_cons, show ∀ (l : List (Nat × Nat)) a, σ ++ a :: l = (σ ++ [a]) ++ l by simp,
        ih, slotValue_append_pair]
      by_cases hV : ∃ k' ∈ V, k' % 2 ^ 256 = slot % 2 ^ 256
      · obtain ⟨k', hk', e⟩ := hV
        rw [ite_eq_left ⟨k', hk', e⟩, ite_eq_left ⟨k', List.mem_cons_of_mem _ hk', e⟩]
      · rw [ite_eq_right hV]
        by_cases e : k % 2 ^ 256 = slot % 2 ^ 256
        · rw [ite_eq_left e, ite_eq_left ⟨k, List.mem_cons_self, e⟩, Nat.mod_eq_of_lt (hlt k), hmod k,
            hmod slot, e]
        · have : ¬ ∃ k' ∈ k :: V, k' % 2 ^ 256 = slot % 2 ^ 256 := by
            rintro ⟨k', hk', e'⟩
            rcases List.mem_cons.mp hk' with rfl | hk'
            · exact e e'
            · exact hV ⟨k', hk', e'⟩
          rw [ite_eq_right e, ite_eq_right this]
  funext slot
  unfold writeBack
  rw [key W call.storage slot]
  split
  · rfl
  · rename_i h
    exact (hkeep slot fun k hk e => h ⟨k, hk, e⟩).symm

/-! ## Stages of sequences -/

/-- A sequence scope: which initial storages and lists of messages a statement covers. -/
abbrev SeqScope := List (Nat × Nat) → List Msg → Prop

/-- Every call the run of \`run\` on \`ms\` from \`σ\` makes, as far as it finishes, is in
\`scope\`. -/
def Along (run : Call → Option Observable) (carry : Carry) (scope : Call → Prop) : SeqScope
  | _, [] => True
  | σ, m :: ms => scope (m.call σ) ∧
    ∀ obs, run (m.call σ) = some obs → Along run carry scope (carry (m.call σ) obs) ms

/-- The sequences of messages of \`M\` from a storage of \`St\`. -/
def within (St : List (Nat × Nat) → Prop) (M : Msg → Prop) : SeqScope :=
  fun σ ms => St σ ∧ ∀ m ∈ ms, M m

/-- The sequences of one message, whose call is in \`scope\`. -/
def single (scope : Call → Prop) : SeqScope := fun σ ms => ∃ m, ms = [m] ∧ scope (m.call σ)

/-- \`StageSeq A B p q carry scope\`: on every sequence of \`scope\` that \`p\` finishes, \`q\`
finishes with the same observables, each call carrying storage to the next with \`carry\`. -/
def StageSeq (A B : Sem) (p : A.Prog) (q : B.Prog) (carry : Carry) (scope : SeqScope) : Prop :=
  ∀ σ ms, scope σ ms → ∀ obss, seqRun A p carry σ ms = some obss → seqRun B q carry σ ms = some obss

theorem StageSeq.refl (A : Sem) (p : A.Prog) (carry : Carry) (scope : SeqScope) :
    StageSeq A A p p carry scope :=
  fun _ _ _ _ h => h

/-- Stages of sequences compose. -/
theorem StageSeq.trans {A B C : Sem} {p : A.Prog} {q : B.Prog} {r : C.Prog} {carry : Carry}
    {scope : SeqScope} (first : StageSeq A B p q carry scope)
    (second : StageSeq B C q r carry scope) : StageSeq A C p r carry scope :=
  fun σ ms h obss ran => second σ ms h obss (first σ ms h obss ran)

/-- A stage of sequences holds on any narrower scope. -/
theorem StageSeq.mono {A B : Sem} {p : A.Prog} {q : B.Prog} {carry : Carry}
    {scope narrower : SeqScope} (stage : StageSeq A B p q carry scope)
    (hn : ∀ σ ms, narrower σ ms → scope σ ms) : StageSeq A B p q carry narrower :=
  fun σ ms h => stage σ ms (hn σ ms h)

/-- A single-call stage holds on every sequence whose calls, as the source runs them, stay in
its scope. -/
theorem StageSeq.of_stage {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (carry : Carry) (stage : Stage A B p q scope) :
    StageSeq A B p q carry (Along (A.run p) carry scope) := by
  intro σ ms
  induction ms generalizing σ with
  | nil => exact fun _ _ h => h
  | cons m ms ih =>
    rintro ⟨hs, hrest⟩ obss hrun
    obtain ⟨obs, os, h1, h2, rfl⟩ := runCalls_cons_eq_some.mp hrun
    exact runCalls_cons_eq_some.mpr
      ⟨obs, os, stage _ hs obs h1, ih _ (hrest obs h1) os h2, rfl⟩

/-- From a set of storages \`St\` closed under the calls of messages of \`M\` that \`run\`
finishes, inside \`scope\`, every call of every sequence stays in \`scope\`. -/
theorem along_of_invariant {run : Call → Option Observable} {carry : Carry}
    {scope : Call → Prop} {St : List (Nat × Nat) → Prop} {M : Msg → Prop}
    (hin : ∀ σ m, St σ → M m → scope (m.call σ))
    (hclosed : ∀ σ m obs, St σ → M m → run (m.call σ) = some obs → St (carry (m.call σ) obs)) :
    ∀ σ ms, within St M σ ms → Along run carry scope σ ms := by
  intro σ ms
  induction ms generalizing σ with
  | nil => exact fun _ => trivial
  | cons m ms ih =>
    rintro ⟨hσ, hms⟩
    have hm := hms m List.mem_cons_self
    exact ⟨hin σ m hσ hm, fun obs h =>
      ih _ ⟨hclosed σ m obs hσ hm h, fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')⟩⟩

/-- **A single-call stage on a storage-invariant scope lifts to sequences.** If every call of a
message of \`M\` from a storage of \`St\` is in the stage's scope, and every storage such a call
of the source leaves (as \`carry\` carries it) is in \`St\` again, the stage holds on every
sequence of messages of \`M\` from a storage of \`St\`. -/
theorem StageSeq.of_invariant {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    {carry : Carry} {St : List (Nat × Nat) → Prop} {M : Msg → Prop}
    (stage : Stage A B p q scope) (hin : ∀ σ m, St σ → M m → scope (m.call σ))
    (hclosed : ∀ σ m obs, St σ → M m → A.run p (m.call σ) = some obs →
      St (carry (m.call σ) obs)) :
    StageSeq A B p q carry (within St M) :=
  (StageSeq.of_stage carry stage).mono (along_of_invariant hin hclosed)

/-- A single-call stage proved from any storage, on every call of a message of \`M\`, holds on
every sequence of messages of \`M\` from any storage, whatever \`carry\` carries. -/
theorem StageSeq.of_anyStorage {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    {M : Msg → Prop} (carry : Carry) (stage : Stage A B p q scope)
    (hin : ∀ σ m, M m → scope (m.call σ)) :
    StageSeq A B p q carry (within (fun _ => True) M) :=
  StageSeq.of_invariant stage (fun σ m _ hm => hin σ m hm) fun _ _ _ _ _ _ => trivial

/-- **Length 1.** A stage of the sequences of one message is a single-call stage. -/
theorem stageSeq_single_iff {A B : Sem} {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (carry : Carry) : StageSeq A B p q carry (single scope) ↔ Stage A B p q scope := by
  constructor
  · intro h call hc obs hrun
    have := h call.storage [Msg.of call] ⟨_, rfl, by rw [Msg.of_call]; exact hc⟩ [obs]
      (by simp only [seqRun, runCalls_singleton, Msg.of_call, hrun]; rfl)
    simp only [seqRun, runCalls_singleton, Msg.of_call, Option.map_eq_some_iff,
      List.cons.injEq, and_true] at this
    obtain ⟨o, ho, rfl⟩ := this
    exact ho
  · rintro h σ _ ⟨m, rfl, hc⟩ obss hrun
    simp only [seqRun, runCalls_singleton, Option.map_eq_some_iff] at hrun ⊢
    obtain ⟨obs, hobs, rfl⟩ := hrun
    exact ⟨obs, h _ hc obs hobs, rfl⟩

/-! ## Specifications of sequences -/

/-- Every call of a run, with its observable, meets \`post\`: \`Each post carry σ ms obss\` when
\`obss\` has one observable for each message of \`ms\` and each meets \`post\` with its call, the
first from \`σ\` and each later one from the storage \`carry\` carries. -/
def Each (post : Call → Observable → Prop) (carry : Carry) :
    List (Nat × Nat) → List Msg → List Observable → Prop
  | _, [], [] => True
  | σ, m :: ms, obs :: os => post (m.call σ) obs ∧ Each post carry (carry (m.call σ) obs) ms os
  | _, _, _ => False

/-- \`SatisfiesSeq S p carry scope pre post\`: \`p\` finishes every sequence of \`scope\` that
meets \`pre\`, with observables that meet \`post\`. -/
def SatisfiesSeq (S : Sem) (p : S.Prog) (carry : Carry) (scope pre : SeqScope)
    (post : List (Nat × Nat) → List Msg → List Observable → Prop) : Prop :=
  ∀ σ ms, scope σ ms → pre σ ms → ∃ obss, seqRun S p carry σ ms = some obss ∧ post σ ms obss

/-- A stage of sequences carries a specification of sequences from its source to its
target. -/
theorem SatisfiesSeq.of_stageSeq {A B : Sem} {p : A.Prog} {q : B.Prog} {carry : Carry}
    {scope pre : SeqScope} {post : List (Nat × Nat) → List Msg → List Observable → Prop}
    (h : SatisfiesSeq A p carry scope pre post) (stage : StageSeq A B p q carry scope) :
    SatisfiesSeq B q carry scope pre post := by
  intro σ ms hs hp
  obtain ⟨obss, hrun, hpost⟩ := h σ ms hs hp
  exact ⟨obss, stage σ ms hs obss hrun, hpost⟩

/-- The precondition of a sequence of one message: its call meets \`pre\`. -/
def singlePre (pre : Call → Prop) : SeqScope := fun σ ms => ∀ m, ms = [m] → pre (m.call σ)

/-- The postcondition of a sequence of one message: it shows one observable, which meets
\`post\` with its call. -/
def singlePost (post : Call → Observable → Prop) :
    List (Nat × Nat) → List Msg → List Observable → Prop :=
  fun σ ms obss => ∀ m, ms = [m] → ∃ obs, obss = [obs] ∧ post (m.call σ) obs

/-- **Length 1.** A specification of the sequences of one message is a single-call
specification. -/
theorem satisfiesSeq_single_iff {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (carry : Carry) :
    SatisfiesSeq S p carry (single scope) (singlePre pre) (singlePost post) ↔
      Satisfies S p scope pre post := by
  constructor
  · intro h call hc hp
    obtain ⟨obss, hrun, hpost⟩ := h call.storage [Msg.of call]
      ⟨_, rfl, by rw [Msg.of_call]; exact hc⟩
      (fun m hm => by cases hm; rw [Msg.of_call]; exact hp)
    obtain ⟨obs, rfl, hobs⟩ := hpost _ rfl
    rw [Msg.of_call] at hobs
    simp only [seqRun, runCalls_singleton, Msg.of_call, Option.map_eq_some_iff,
      List.cons.injEq, and_true] at hrun
    obtain ⟨o, ho, rfl⟩ := hrun
    exact ⟨o, ho, hobs⟩
  · rintro h σ _ ⟨m, rfl, hc⟩ hp
    obtain ⟨obs, hrun, hpost⟩ := h _ hc (hp m rfl)
    refine ⟨[obs], by simp only [seqRun, runCalls_singleton, hrun]; rfl, ?_⟩
    rintro m' hm'
    cases hm'
    exact ⟨obs, rfl, hpost⟩

/-- A run of a program that satisfies a specification meets its postcondition. -/
theorem Satisfies.post_of_run {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (h : Satisfies S p scope pre post) {call : Call}
    (hc : scope call) (hp : pre call) {obs : Observable} (hrun : S.run p call = some obs) :
    post call obs := by
  obtain ⟨o, ho, hpost⟩ := h call hc hp
  rw [hrun] at ho
  cases ho
  exact hpost

/-- A specification holds with any weaker postcondition. -/
theorem Satisfies.mono {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post post' : Call → Observable → Prop} (h : Satisfies S p scope pre post)
    (hpost : ∀ call obs, scope call → pre call → post call obs → post' call obs) :
    Satisfies S p scope pre post' := by
  intro call hc hp
  obtain ⟨obs, hrun, hq⟩ := h call hc hp
  exact ⟨obs, hrun, hpost call obs hc hp hq⟩

/-- **A single-call specification on a storage-invariant scope lifts to sequences.** If every
call of a message of \`M\` from a storage of \`St\` is in the scope and meets the precondition,
and every storage a call that meets the postcondition leaves (as \`carry\` carries it) is in
\`St\` again, then \`p\` finishes every sequence of messages of \`M\` from a storage of \`St\`, and
every call of it meets the postcondition. -/
theorem Satisfies.toSeq {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} {carry : Carry} {St : List (Nat × Nat) → Prop}
    {M : Msg → Prop} (h : Satisfies S p scope pre post)
    (hin : ∀ σ m, St σ → M m → scope (m.call σ) ∧ pre (m.call σ))
    (hclosed : ∀ σ m obs, St σ → M m → post (m.call σ) obs → St (carry (m.call σ) obs)) :
    SatisfiesSeq S p carry (within St M) (fun _ _ => True) (Each post carry) := by
  intro σ ms hs _
  induction ms generalizing σ with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons m ms ih =>
    obtain ⟨hσ, hms⟩ := hs
    have hm := hms m List.mem_cons_self
    obtain ⟨hc, hp⟩ := hin σ m hσ hm
    obtain ⟨obs, hrun, hpost⟩ := h _ hc hp
    obtain ⟨os, hos, heach⟩ :=
      ih _ ⟨hclosed σ m obs hσ hm hpost, fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')⟩
    exact ⟨obs :: os, runCalls_cons_eq_some.mpr ⟨obs, os, hrun, hos, rfl⟩, hpost, heach⟩

/-- \`Each\` of a postcondition that implies another implies \`Each\` of the other. -/
theorem Each.mono {post post' : Call → Observable → Prop} {carry : Carry}
    (h : ∀ call obs, post call obs → post' call obs) :
    ∀ {σ ms obss}, Each post carry σ ms obss → Each post' carry σ ms obss
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨hp, hrest⟩ => ⟨h _ _ hp, Each.mono h hrest⟩

/-! ## Refinement of sequences, and specifications carried to bytecode -/

/-- \`code\` implements \`contract\` on every sequence of \`scope\`: SolidCore with \`fuel\` and
EthLib both finish every call and show the same observables, each call starting from the
storage \`carry\` carries from the one before. -/
def RefinesSeqOn (fuel : Nat) (contract : SolidCore.Solidity.TypeCheck.CheckedContract)
    (code : ByteArray) (carry : Carry) (scope : SeqScope) : Prop :=
  ∀ σ ms, scope σ ms →
    ∃ obss, seqRun (solidCore fuel) contract carry σ ms = some obss ∧
      seqRun ethLib code carry σ ms = some obss

/-- A stage of sequences from SolidCore to EthLib gives \`RefinesSeqOn\` on the sequences
SolidCore finishes. -/
theorem refinesSeqOn_of_stageSeq {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {carry : Carry} {scope : SeqScope}
    (h : StageSeq (solidCore fuel) ethLib contract code carry scope)
    (fin : ∀ σ ms, scope σ ms → (seqRun (solidCore fuel) contract carry σ ms).isSome) :
    RefinesSeqOn fuel contract code carry scope := by
  intro σ ms hs
  obtain ⟨obss, hobss⟩ := Option.isSome_iff_exists.mp (fin σ ms hs)
  exact ⟨obss, hobss, h σ ms hs obss hobss⟩

/-- \`RefinesSeqOn\` is a stage of sequences from SolidCore to EthLib. -/
theorem stageSeq_of_refinesSeqOn {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {carry : Carry} {scope : SeqScope} (h : RefinesSeqOn fuel contract code carry scope) :
    StageSeq (solidCore fuel) ethLib contract code carry scope := by
  intro σ ms hs obss hrun
  obtain ⟨obss', h1, h2⟩ := h σ ms hs
  have : obss' = obss := Option.some.inj (h1.symm.trans hrun)
  exact this ▸ h2

/-- **Length 1.** Refinement of the sequences of one message is \`Refines\`. -/
theorem refinesSeqOn_single_iff {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {scope : Call → Prop} (carry : Carry) :
    RefinesSeqOn fuel contract code carry (single scope) ↔ Refines fuel contract code scope := by
  constructor
  · intro h call hc
    obtain ⟨obss, h1, h2⟩ := h call.storage [Msg.of call] ⟨_, rfl, by rw [Msg.of_call]; exact hc⟩
    simp only [seqRun, runCalls_singleton, Msg.of_call, Option.map_eq_some_iff] at h1 h2
    obtain ⟨o1, ho1, rfl⟩ := h1
    obtain ⟨o2, ho2, e⟩ := h2
    cases e
    exact ⟨o1, ho1, ho2⟩
  · rintro h σ _ ⟨m, rfl, hc⟩
    obtain ⟨obs, h1, h2⟩ := h _ hc
    refine ⟨[obs], ?_, ?_⟩
    · show runCalls _ _ _ _ = _
      simp only [runCalls_singleton]
      exact congrArg (Option.map _) h1
    · show runCalls _ _ _ _ = _
      simp only [runCalls_singleton]
      exact congrArg (Option.map _) h2

/-- A specification of sequences SolidCore satisfies holds of bytecode that refines it on
those sequences. -/
theorem bytecodeSeq_of_refines {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {carry : Carry} {scope pre : SeqScope}
    {post : List (Nat × Nat) → List Msg → List Observable → Prop}
    (spec : SatisfiesSeq (solidCore fuel) contract carry scope pre post)
    (refines : RefinesSeqOn fuel contract code carry scope) :
    SatisfiesSeq ethLib code carry scope pre post :=
  spec.of_stageSeq (stageSeq_of_refinesSeqOn refines)

/-- A specification of sequences SolidCore satisfies holds of the bytecode a compiler produces
through lowered MIR and EVM IR, given each of its stages on those sequences; the sequence form
of \`bytecode_of_stages\`. -/
theorem bytecodeSeq_of_stages {fuel : Nat} {mirSem evmirSem : Sem}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {carry : Carry} {scope pre : SeqScope}
    {post : List (Nat × Nat) → List Msg → List Observable → Prop}
    (spec : SatisfiesSeq (solidCore fuel) contract carry scope pre post)
    (lowering : StageSeq (solidCore fuel) mirSem contract mir carry scope)
    (backend : StageSeq mirSem evmirSem mir evmir carry scope)
    (assembly : StageSeq evmirSem ethLib evmir code carry scope) :
    SatisfiesSeq ethLib code carry scope pre post :=
  spec.of_stageSeq ((lowering.trans backend).trans assembly)

/-- **Single-call stages on a storage-invariant scope give the bytecode's sequences.** A
single-call specification SolidCore satisfies and single-call stages through lowered MIR and EVM
IR, with a set of storages \`St\` from which every call of a message of \`M\` is in the scope and
meets the precondition, and which every call meeting the postcondition leaves storage in, give:
the bytecode finishes every sequence of messages of \`M\` from a storage of \`St\`, and every call
of it meets the postcondition. -/
theorem bytecodeSeq_of_stages_invariant {fuel : Nat} {mirSem evmirSem : Sem}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} {carry : Carry} {St : List (Nat × Nat) → Prop}
    {M : Msg → Prop}
    (spec : Satisfies (solidCore fuel) contract scope pre post)
    (lowering : Stage (solidCore fuel) mirSem contract mir scope)
    (backend : Stage mirSem evmirSem mir evmir scope)
    (assembly : Stage evmirSem ethLib evmir code scope)
    (hin : ∀ σ m, St σ → M m → scope (m.call σ) ∧ pre (m.call σ))
    (hclosed : ∀ σ m obs, St σ → M m → post (m.call σ) obs → St (carry (m.call σ) obs)) :
    SatisfiesSeq ethLib code carry (within St M) (fun _ _ => True) (Each post carry) :=
  (spec.toSeq hin hclosed).of_stageSeq
    (StageSeq.of_invariant ((lowering.trans backend).trans assembly)
      (fun σ m hσ hm => (hin σ m hσ hm).1) fun σ m obs hσ hm hrun =>
        hclosed σ m obs hσ hm
          (spec.post_of_run (hin σ m hσ hm).1 (hin σ m hσ hm).2 hrun))

/-! ## \`Sequence.lean\`'s sequences -/

/-- \`Sequence.lean\`'s \`runSeq\`, whose carried list depends on the observable only, is
\`runCalls\` with that carry. -/
theorem runCalls_eq_runSeq (run : Call → Option Observable)
    (next : Observable → List (Nat × Nat)) :
    ∀ σ ms, runCalls run (fun _ obs => next obs) σ ms = runSeq run next σ ms
  | _, [] => rfl
  | σ, m :: ms => by
    simp only [runCalls, runSeq]
    cases run (m.call σ) with
    | none => rfl
    | some obs => simp only [runCalls_eq_runSeq run next _ ms]

/-- \`Sequence.lean\`'s \`RefinesSeq\` from \`σ0\` gives \`RefinesSeqOn\` on the sequences from
\`σ0\`. -/
theorem refinesSeqOn_of_refinesSeq {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {next : Observable → List (Nat × Nat)} {σ0 : List (Nat × Nat)} {scope : Msg → Prop}
    (h : RefinesSeq fuel contract code next σ0 scope) :
    RefinesSeqOn fuel contract code (fun _ obs => next obs) (within (· = σ0) scope) := by
  rintro σ ms ⟨rfl, hms⟩
  obtain ⟨obss, h1, h2, -⟩ := h ms.length ms (Nat.le_refl _) hms
  exact ⟨obss, (runCalls_eq_runSeq _ _ _ _).trans h1, (runCalls_eq_runSeq _ _ _ _).trans h2⟩

/-- \`RefinesSeqOn\` on the sequences from \`σ0\` gives \`Sequence.lean\`'s \`RefinesSeq\` when
\`next\` carries every observable but the last of each run exactly. -/
theorem refinesSeq_of_refinesSeqOn {fuel : Nat}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {code : ByteArray}
    {next : Observable → List (Nat × Nat)} {σ0 : List (Nat × Nat)} {scope : Msg → Prop}
    (h : RefinesSeqOn fuel contract code (fun _ obs => next obs) (within (· = σ0) scope))
    (exact : ∀ ms obss, (∀ m ∈ ms, scope m) →
      runSeq (Source.run fuel contract) next σ0 ms = some obss →
        ∀ obs ∈ obss.dropLast, Exact next obs) :
    RefinesSeq fuel contract code next σ0 scope := by
  intro n ms _ hms
  obtain ⟨obss, h1, h2⟩ := h σ0 ms ⟨rfl, hms⟩
  have h1' := (runCalls_eq_runSeq _ _ _ _).symm.trans h1
  exact ⟨obss, h1', (runCalls_eq_runSeq _ _ _ _).symm.trans h2, exact ms obss hms h1'⟩

end SolidCore.Refinement
