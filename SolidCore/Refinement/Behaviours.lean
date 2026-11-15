import SolidCore.Refinement.Spec

/-!
# Behaviours, totality and the direction of refinement

`Stage A B p q scope` (solar's `SolarTV.Stage`) is a forward, partial statement: every
observable the source `p` gives on a call in `scope`, the target `q` gives too. On a call
where `p` gives nothing (it runs out of fuel, diverges, or uses something its semantics leaves
undefined) a stage says nothing about `q` at all, so a stage from a source that never finishes
holds for every target (`Stage.of_never`). A chain of stages is therefore only as strong as
the totality of its first source.

This module states what the end-to-end theorems actually need and proves how the three forms
relate, for semantics whose `run` is a function (every `Sem`), so each program has at most
one observable per call:

* `Defined S p scope`: `p` finishes every call of `scope`.
* `Backward A B p q scope`: every observable of the target is an observable of the source
  (target behaviours ⊆ source behaviours, the direction a user of compiled code relies on). Since
  an `Observable` is success, output (return or revert data), logs and final storage, this
  covers reverts and their data, return data, logs and storage at once.
* `Total A B p q scope`: on every call of `scope` both sides finish with the same observable.
  `Refines` is `Total (solidCore fuel) ethLib` (`refines_iff_total`).

`total_iff_stage` and `total_iff_backward`: `Total` is a stage whose source is defined on the
scope, and equally a backward simulation whose target is defined on it. `Total.trans` and
`Backward.trans` compose. `Satisfies.total_of_stage` is the point of the module: a stage whose
source satisfies a total specification is `Total` on the specified calls, so
`bytecode_total_of_stages` gives target ⊆ source end to end, with no vacuous case.

Fuel. SolidCore's `Source.run fuel` returns `none` when the statement fuel runs out, so a run that
runs out of fuel refutes `Total`, `Refines` and `Satisfies` rather than satisfying them; solar's
MIR and EVM IR semantics take the end some fuel reaches (`SolarTV.Machine.Layer.result`), so they
have no fuel cut-off at all. EthLib's `Target.run` is bounded by gas: running out of gas is a failed
call, an `Observable` with `success = false`, never `none`; a theorem at `gasLimit` where the source
succeeds must show the bytecode does not run out.

Failures. `ethLib` and `solidCore` both satisfy solar's `Sem.FailureConvention` (a failed call logs
nothing and keeps the call's storage; `ethLib_failureConvention`, `solidCore_failureConvention`),
and `Total` and `Backward` carry it from source to target.

Discrimination. The relations are not trivial: on the semantics `Fixed` whose programs are their own
observables, a stage between two programs that differ in exactly one field of `Observable`
(success, output, logs or one storage slot) is false (`stage_rejects_*`). A relation that related
everything would prove those false statements' negations false, so these theorems would not check.
-/

namespace SolidCore.Refinement

variable {A B C : Sem}

/-- `p` finishes every call of `scope`. -/
def Defined (S : Sem) (p : S.Prog) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → (S.run p call).isSome

/-- Every observable `q` gives on a call of `scope` is the observable `p` gives: the target's
behaviours are among the source's. -/
def Backward (A B : Sem) (p : A.Prog) (q : B.Prog) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∀ obs, B.run q call = some obs → A.run p call = some obs

/-- On every call of `scope` both programs finish, with the same observable. -/
def Total (A B : Sem) (p : A.Prog) (q : B.Prog) (scope : Call → Prop) : Prop :=
  ∀ call, scope call → ∃ obs, A.run p call = some obs ∧ B.run q call = some obs

/-! ## The three forms -/

theorem Total.stage {p : A.Prog} {q : B.Prog} {scope : Call → Prop} (h : Total A B p q scope) :
    Stage A B p q scope := by
  intro call hc obs hrun
  obtain ⟨obs', h1, h2⟩ := h call hc
  rw [hrun] at h1
  cases h1
  exact h2

theorem Total.backward {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Total A B p q scope) : Backward A B p q scope := by
  intro call hc obs hrun
  obtain ⟨obs', h1, h2⟩ := h call hc
  rw [hrun] at h2
  cases h2
  exact h1

theorem Total.source_defined {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Total A B p q scope) : Defined A p scope := by
  intro call hc
  obtain ⟨obs, h1, -⟩ := h call hc
  simp [h1]

theorem Total.target_defined {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (h : Total A B p q scope) : Defined B q scope := by
  intro call hc
  obtain ⟨obs, -, h2⟩ := h call hc
  simp [h2]

/-- A total refinement is exactly a stage whose source finishes on the scope. -/
theorem total_iff_stage {p : A.Prog} {q : B.Prog} {scope : Call → Prop} :
    Total A B p q scope ↔ Stage A B p q scope ∧ Defined A p scope := by
  refine ⟨fun h => ⟨h.stage, h.source_defined⟩, fun ⟨st, df⟩ call hc => ?_⟩
  obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp (df call hc)
  exact ⟨obs, hobs, st call hc obs hobs⟩

/-- A total refinement is exactly a backward simulation whose target finishes on the scope. -/
theorem total_iff_backward {p : A.Prog} {q : B.Prog} {scope : Call → Prop} :
    Total A B p q scope ↔ Backward A B p q scope ∧ Defined B q scope := by
  refine ⟨fun h => ⟨h.backward, h.target_defined⟩, fun ⟨bw, df⟩ call hc => ?_⟩
  obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp (df call hc)
  exact ⟨obs, bw call hc obs hobs, hobs⟩

/-- A stage from a source that finishes on the scope is a backward simulation: every target
observable is the source's. -/
theorem Stage.backward_of_defined {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (st : Stage A B p q scope) (df : Defined A p scope) : Backward A B p q scope :=
  (total_iff_stage.mpr ⟨st, df⟩).backward

/-! ## Composition -/

theorem Total.trans {p : A.Prog} {q : B.Prog} {r : C.Prog} {scope : Call → Prop}
    (first : Total A B p q scope) (second : Total B C q r scope) : Total A C p r scope := by
  intro call hc
  obtain ⟨obs, h1, h2⟩ := first call hc
  obtain ⟨obs', h2', h3⟩ := second call hc
  rw [h2] at h2'
  cases h2'
  exact ⟨obs, h1, h3⟩

/-- A total first stage and plain stages after it compose to a total refinement: the
totality of the whole chain is the totality of its first source. -/
theorem Total.trans_stage {p : A.Prog} {q : B.Prog} {r : C.Prog} {scope : Call → Prop}
    (first : Total A B p q scope) (second : Stage B C q r scope) : Total A C p r scope :=
  total_iff_stage.mpr ⟨first.stage.trans second, first.source_defined⟩

theorem Backward.trans {p : A.Prog} {q : B.Prog} {r : C.Prog} {scope : Call → Prop}
    (first : Backward A B p q scope) (second : Backward B C q r scope) :
    Backward A C p r scope :=
  fun call hc obs h3 => first call hc obs (second call hc obs h3)

theorem Total.refl (A : Sem) (p : A.Prog) {scope : Call → Prop} (df : Defined A p scope) :
    Total A A p p scope :=
  total_iff_stage.mpr ⟨fun _ _ _ h => h, df⟩

theorem Total.mono {p : A.Prog} {q : B.Prog} {scope narrower : Call → Prop}
    (h : Total A B p q scope) (within : ∀ call, narrower call → scope call) :
    Total A B p q narrower :=
  fun call hc => h call (within call hc)

theorem Backward.mono {p : A.Prog} {q : B.Prog} {scope narrower : Call → Prop}
    (h : Backward A B p q scope) (within : ∀ call, narrower call → scope call) :
    Backward A B p q narrower :=
  fun call hc => h call (within call hc)

/-! ## Vacuity of a bare stage -/

/-- A stage from a source that finishes no call of the scope holds for every target. -/
theorem Stage.of_never {p : A.Prog} (q : B.Prog) {scope : Call → Prop}
    (never : ∀ call, scope call → A.run p call = none) : Stage A B p q scope := by
  intro call hc obs hrun
  rw [never call hc] at hrun
  cases hrun

/-- A total refinement rules that out: one call of the scope the source does not finish
refutes it, whatever the target. -/
theorem Total.not_of_none {p : A.Prog} {q : B.Prog} {scope : Call → Prop} {call : Call}
    (hc : scope call) (none_ : A.run p call = none) : ¬ Total A B p q scope := by
  intro h
  obtain ⟨obs, h1, -⟩ := h call hc
  rw [none_] at h1
  cases h1

/-! ## Specifications -/

/-- A stage from a program that satisfies a total specification is a total refinement on the
calls the specification covers. -/
theorem Satisfies.total_of_stage {p : A.Prog} {q : B.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (spec : Satisfies A p scope pre post)
    (st : Stage A B p q scope) : Total A B p q (fun call => scope call ∧ pre call) := by
  intro call ⟨hc, hp⟩
  obtain ⟨obs, hrun, -⟩ := spec call hc hp
  exact ⟨obs, hrun, st call hc obs hrun⟩

/-- A backward simulation onto a defined target carries a specification from the source to
the target. -/
theorem Satisfies.of_backward {p : A.Prog} {q : B.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (spec : Satisfies A p scope pre post)
    (bw : Backward A B p q scope) (df : Defined B q scope) : Satisfies B q scope pre post := by
  intro call hc hp
  obtain ⟨obs, hrun, hpost⟩ := spec call hc hp
  obtain ⟨obs', h'⟩ := Option.isSome_iff_exists.mp (df call hc)
  have := bw call hc obs' h'
  rw [hrun] at this
  cases this
  exact ⟨obs, h', hpost⟩

/-- The target of a specification-satisfying program meets the specification on every
observable it gives, not only on one. -/
theorem Satisfies.post_of_target {S : Sem} {p : S.Prog} {scope pre : Call → Prop}
    {post : Call → Observable → Prop} (spec : Satisfies S p scope pre post) {call : Call}
    (hc : scope call) (hp : pre call) {obs : Observable} (hrun : S.run p call = some obs) :
    post call obs := by
  obtain ⟨obs', h', hpost⟩ := spec call hc hp
  rw [hrun] at h'
  cases h'
  exact hpost

/-! ## SolidCore to EthLib -/

theorem refines_iff_total {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} :
    Refines fuel contract code scope ↔ Total (solidCore fuel) ethLib contract code scope :=
  Iff.rfl

/-- Every observable solar's bytecode gives on a call of the scope is SolidCore's for the
same call: its success, return or revert data, logs and final storage. -/
theorem Refines.backward {fuel : Nat} {contract : SolidCore.Solidity.TypeCheck.CheckedContract}
    {code : ByteArray} {scope : Call → Prop} (h : Refines fuel contract code scope) {call : Call}
    (hc : scope call) {obs : Observable} (hrun : Target.run code call = some obs) :
    Source.run fuel contract call = some obs :=
  (refines_iff_total.mp h).backward call hc obs hrun

/-- The end-to-end form through a compiler's stages, as `bytecode_of_stages` states it, gives a
total refinement from SolidCore to the bytecode on the specified calls, so the bytecode's
behaviours there are SolidCore's, and nothing in it is vacuous: SolidCore finishes each such
call (the specification says so), and each stage then forces the next language to finish it
with the same observable. -/
theorem bytecode_total_of_stages {fuel : Nat} {mirSem evmirSem : Sem}
    {contract : SolidCore.Solidity.TypeCheck.CheckedContract} {mir : mirSem.Prog}
    {evmir : evmirSem.Prog} {code : ByteArray} {scope : Call → Prop} {pre : Call → Prop}
    {post : Call → Observable → Prop}
    (spec : Satisfies (solidCore fuel) contract scope pre post)
    (lowering : Stage (solidCore fuel) mirSem contract mir scope)
    (backend : Stage mirSem evmirSem mir evmir scope)
    (assembly : Stage evmirSem ethLib evmir code scope) :
    Refines fuel contract code (fun call => scope call ∧ pre call) ∧
      Satisfies ethLib code scope pre post :=
  ⟨spec.total_of_stage ((lowering.trans backend).trans assembly),
    bytecode_of_stages spec lowering backend assembly⟩

/-! ## Failures roll back -/

theorem ethLib_failureConvention : ethLib.FailureConvention := by
  intro code call obs hrun hfail
  simp only [ethLib, Target.run] at hrun
  split at hrun
  · cases hrun
  · cases hrun
    simp only at hfail ⊢
    simp [hfail]

theorem solidCore_failureConvention (fuel : Nat) : (solidCore fuel).FailureConvention := by
  intro contract call obs hrun hfail
  simp only [solidCore, Source.run, Option.map_eq_some_iff] at hrun
  obtain ⟨r, -, rfl⟩ := hrun
  simp only [Source.observe] at hfail ⊢
  simp [hfail]

/-- A backward simulation from a semantics that rolls failures back gives a target whose
failures roll back too. -/
theorem Backward.failure {p : A.Prog} {q : B.Prog} {scope : Call → Prop}
    (bw : Backward A B p q scope) (conv : A.FailureConvention) {call : Call} (hc : scope call)
    {obs : Observable} (hrun : B.run q call = some obs) (hfail : obs.success = false) :
    obs.logs = [] ∧ obs.storage = slotValue call.storage :=
  conv p call obs (bw call hc obs hrun) hfail

/-! ## The relations tell observables apart

`Fixed` is the semantics whose program is the observable it gives on every call. A stage between two
of its programs holds exactly when they are equal, so each of the four fields of `Observable`
separates stages; a relation that related every pair would fail each `stage_rejects_*` below. -/

/-- Every call gives the program itself. -/
def Fixed : Sem := { Prog := Observable, run := fun obs _ => some obs }

/-- Some call is in scope. -/
def Inhabited' (scope : Call → Prop) : Prop := ∃ call, scope call

theorem Fixed.stage_iff {o o' : Observable} {scope : Call → Prop} (h : Inhabited' scope) :
    Stage Fixed Fixed o o' scope ↔ o = o' := by
  obtain ⟨call, hc⟩ := h
  constructor
  · intro st
    have := st call hc o rfl
    simp only [Fixed, Option.some.injEq] at this
    exact this.symm
  · rintro rfl
    exact fun _ _ _ h => h

theorem Fixed.total_iff {o o' : Observable} {scope : Call → Prop} (h : Inhabited' scope) :
    Total Fixed Fixed o o' scope ↔ o = o' := by
  constructor
  · intro t
    exact (Fixed.stage_iff h).mp t.stage
  · rintro rfl
    exact total_iff_stage.mpr ⟨(Fixed.stage_iff h).mpr rfl, fun _ _ => rfl⟩

theorem Fixed.backward_iff {o o' : Observable} {scope : Call → Prop} (h : Inhabited' scope) :
    Backward Fixed Fixed o o' scope ↔ o = o' := by
  have d : Defined Fixed o' scope := fun _ _ => rfl
  constructor
  · intro bw
    exact (Fixed.total_iff h).mp (total_iff_backward.mpr ⟨bw, d⟩)
  · rintro rfl
    exact fun _ _ _ h => h

/-- The call with no call data, no value and empty storage. -/
def emptyCall : Call := ⟨.empty, 0, []⟩

theorem everywhere : Inhabited' (fun _ : Call => True) := ⟨emptyCall, trivial⟩

/-- A success and a failure with the same data are told apart. -/
theorem stage_rejects_success :
    ¬ Stage Fixed Fixed (⟨true, [], [], fun _ => 0⟩ : Observable) ⟨false, [], [], fun _ => 0⟩
      (fun _ => True) := by
  intro st
  have := (Fixed.stage_iff everywhere).mp st
  simp at this

/-- Two reverts with different revert data are told apart. -/
theorem stage_rejects_output :
    ¬ Stage Fixed Fixed (⟨false, [1], [], fun _ => 0⟩ : Observable) ⟨false, [2], [], fun _ => 0⟩
      (fun _ => True) := by
  intro st
  have := (Fixed.stage_iff everywhere).mp st
  simp at this

/-- Two successes that log differently are told apart. -/
theorem stage_rejects_logs :
    ¬ Stage Fixed Fixed (⟨true, [], [([1], [])], fun _ => 0⟩ : Observable)
      ⟨true, [], [], fun _ => 0⟩ (fun _ => True) := by
  intro st
  have := (Fixed.stage_iff everywhere).mp st
  simp at this

/-- Two successes that leave one slot differently are told apart. -/
theorem stage_rejects_storage :
    ¬ Stage Fixed Fixed (⟨true, [], [], fun s => if s = 7 then 1 else 0⟩ : Observable)
      ⟨true, [], [], fun _ => 0⟩ (fun _ => True) := by
  intro st
  have h := (Fixed.stage_iff everywhere).mp st
  have := congrArg (fun o : Observable => o.storage 7) h
  simp at this

/-- A source that never finishes makes a bare stage hold of every target, and a total
refinement of none: here, the target that always succeeds. -/
theorem never_stage_total :
    Stage (⟨Unit, fun _ _ => none⟩ : Sem) Fixed () ⟨true, [], [], fun _ => 0⟩ (fun _ => True) ∧
      ¬ Total (⟨Unit, fun _ _ => none⟩ : Sem) Fixed () ⟨true, [], [], fun _ => 0⟩
        (fun _ => True) :=
  ⟨Stage.of_never _ (fun _ _ => rfl), Total.not_of_none (call := emptyCall) trivial rfl⟩


/-- info: 'SolidCore.Refinement.total_iff_backward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms total_iff_backward

/-- info: 'SolidCore.Refinement.Total.trans_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Total.trans_stage

/--
info: 'SolidCore.Refinement.bytecode_total_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bytecode_total_of_stages

/--
info: 'SolidCore.Refinement.ethLib_failureConvention' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ethLib_failureConvention

/-- info: 'SolidCore.Refinement.stage_rejects_storage' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage_rejects_storage

end SolidCore.Refinement
