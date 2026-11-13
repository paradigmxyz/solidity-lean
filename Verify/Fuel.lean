import Verify.Basic

/-!
# Termination with as much fuel as a call needs

A model with a loop needs interpreter fuel that grows with its arguments: each call finishes
at some fuel (`ImplementsSome`, `TripleSome`: for every call, some fuel). That is not one
fuel for every call, and no fuel-monotonicity lemma turns the one into the other: for every
call some fuel is not some fuel for every call. This module gives the two honest ways on.

**Pointwise, without any monotonicity.** `runAny c call` is SolidCore's run at the least fuel
that finishes the call (`none` if none does): the same definition as the composition's
`Final.solidCoreAny`'s run, so `solidCoreAny.run c call = runAny c call` is `rfl`.
`ImplementsAny` and `TripleAny` state the model and the triple against it, and
`tripleAny_of_wp` is the generator's soundness for them. `TripleAny` is exactly the source's
termination and correctness that `Final.compose` takes with `S := solidCoreAny`.

**Through fuel stability, as an explicit hypothesis.** `FuelStable c` (the composition's
`Final.FuelStable`, the same definition): more fuel does not change a finished run. It speaks only
of runs that finish (`some`), so an out-of-fuel run (`none`) may become any result, a revert
included, with more fuel, while a revert or a return at some fuel stays that result at every
higher fuel; a revert never stands for running out of fuel. Given it:

* `runAny_of_run`, `implementsAny_of_some`, `tripleAny_of_some`: the some-fuel forms give the
  least-fuel ones;
* `triple_of_within`: a **bounded** some-fuel triple (`TripleWithin B`: every call finishes at
  some fuel at most `B`) gives the fixed-fuel `Triple B`. The bound is a hypothesis to prove
  for the contract (for a loop over a word, from the word's bound), not an assumption.

`FuelStable` is not proved here: `Verify.FuelStable` derives it (`fuelStable_of_ctorStable`) from
`SolidCore.Refinement.Source.run_fuel_mono`, `Source.run`'s fuel monotonicity along every path,
given the constructor's stability (`CtorStable`) as a hypothesis.
-/

namespace SolidCore.Verify

open SolidCore.Refinement

open Classical in
/-- SolidCore's run of `c` on `call` at the least fuel that finishes it; `none` when no fuel
does. The same as `Final.solidCoreAny`'s run. -/
noncomputable def runAny (c : SolidCore.Solidity.TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  if h : ∃ n, (Source.run n c call).isSome then Source.run (Nat.find h) c call else none

/-- More fuel does not change a finished run of `c` (the same as `Final.FuelStable`). -/
def FuelStable (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Prop :=
  ∀ n m call obs, n ≤ m → Source.run n c call = some obs → Source.run m c call = some obs

theorem runAny_isSome_iff {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : Call} :
    (runAny c call).isSome ↔ ∃ n, (Source.run n c call).isSome := by
  classical
  unfold runAny
  constructor
  · intro h
    by_contra hne
    rw [dif_neg hne] at h
    simp at h
  · intro hex
    rw [dif_pos hex]
    exact Nat.find_spec hex

/-- A result of `runAny` is SolidCore's result at some fuel. -/
theorem runAny_spec {c : SolidCore.Solidity.TypeCheck.CheckedContract} {call : Call}
    {obs : Observable} (h : runAny c call = some obs) : ∃ n, Source.run n c call = some obs := by
  classical
  unfold runAny at h
  by_cases hex : ∃ n, (Source.run n c call).isSome
  · rw [dif_pos hex] at h; exact ⟨_, h⟩
  · rw [dif_neg hex] at h; cases h

/-- With fuel stability, a run that finishes at some fuel is `runAny`'s. -/
theorem runAny_of_run {c : SolidCore.Solidity.TypeCheck.CheckedContract} (stable : FuelStable c)
    {fuel : Nat} {call : Call} {obs : Observable} (h : Source.run fuel c call = some obs) :
    runAny c call = some obs := by
  classical
  have hex : ∃ n, (Source.run n c call).isSome := ⟨fuel, by simp [h]⟩
  unfold runAny
  rw [dif_pos hex]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  have hle : Nat.find hex ≤ fuel := Nat.find_min' hex (by simp [h])
  have := stable _ _ _ _ hle ho
  rw [h] at this
  rw [ho, Option.some.inj this]

/-- `model` implements `c` on `scope` with as much fuel as each call needs. -/
def ImplementsAny (c : SolidCore.Solidity.TypeCheck.CheckedContract) (scope : Call → Prop)
    (args : Call → List Nat) (model : List Nat → SolM (List Nat)) : Prop :=
  ∀ call, scope call →
    runAny c call = some (observe (initStorage call) (model (args call) (initStorage call)))

/-- Every call of the scope that meets `pre` finishes with as much fuel as it needs, with an
observable that meets `post`. -/
def TripleAny (c : SolidCore.Solidity.TypeCheck.CheckedContract) (scope : Call → Prop)
    (pre : Call → Prop) (post : Call → Observable → Prop) : Prop :=
  ∀ call, scope call → pre call → ∃ obs, runAny c call = some obs ∧ post call obs

/-- The generator's soundness with as much fuel as each call needs; no fuel monotonicity. -/
theorem tripleAny_of_wp {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {scope : Call → Prop} {args : Call → List Nat} {model : List Nat → SolM (List Nat)}
    {pre : Call → Prop} {post : Call → Observable → Prop}
    (himpl : ImplementsAny c scope args model)
    (hvc : ∀ call, scope call → pre call → vc model args post call) :
    TripleAny c scope pre post := by
  intro call hs hp
  have h := hvc call hs hp
  simp only [vc, wp_eq] at h
  refine ⟨_, himpl call hs, ?_⟩
  revert h
  rcases model (args call) (initStorage call) with e | ⟨out, s'⟩ <;> exact id

/-- `TripleAny` gives every call of the scope that meets `pre` a finishing fuel. -/
theorem TripleAny.some {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (h : TripleAny c scope pre post) : TripleSome c scope pre post := by
  intro call hs hp
  obtain ⟨obs, hrun, hpost⟩ := h call hs hp
  obtain ⟨n, hn⟩ := runAny_spec hrun
  exact ⟨n, obs, hn, hpost⟩

theorem implementsAny_of_some {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (stable : FuelStable c) {scope : Call → Prop} {args : Call → List Nat}
    {model : List Nat → SolM (List Nat)} (h : ImplementsSome c scope args model) :
    ImplementsAny c scope args model := by
  intro call hs
  obtain ⟨fuel, hrun⟩ := h call hs
  exact runAny_of_run stable hrun

theorem tripleAny_of_some {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (stable : FuelStable c) {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (h : TripleSome c scope pre post) : TripleAny c scope pre post := by
  intro call hs hp
  obtain ⟨fuel, obs, hrun, hpost⟩ := h call hs hp
  exact ⟨obs, runAny_of_run stable hrun, hpost⟩

/-- Every call of the scope that meets `pre` finishes at some fuel at most `B`, with an
observable that meets `post`. -/
def TripleWithin (B : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract)
    (scope : Call → Prop) (pre : Call → Prop) (post : Call → Observable → Prop) : Prop :=
  ∀ call, scope call → pre call → ∃ fuel ≤ B, ∃ obs, Source.run fuel c call = some obs ∧ post call obs

/-- **A bounded some-fuel triple is a fixed-fuel triple**, given fuel stability. -/
theorem triple_of_within {B : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (stable : FuelStable c) {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (h : TripleWithin B c scope pre post) : Triple B c scope pre post := by
  intro call hs hp
  obtain ⟨fuel, hle, obs, hrun, hpost⟩ := h call hs hp
  have hB := stable _ _ _ _ hle hrun
  refine ⟨by simp [hB], fun o ho => ?_⟩
  rw [hB] at ho
  cases ho
  exact hpost

/-- A fixed-fuel triple is a least-fuel one, given fuel stability. -/
theorem Triple.any {fuel : Nat} {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (stable : FuelStable c) {scope pre : Call → Prop} {post : Call → Observable → Prop}
    (h : Triple fuel c scope pre post) : TripleAny c scope pre post :=
  tripleAny_of_some stable h.some

end SolidCore.Verify
