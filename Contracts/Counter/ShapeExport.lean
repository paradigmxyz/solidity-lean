import Contracts.Counter.Shape
import Contracts.Counter.Headline
import Verify.ShapeBundle

/-!
# Counter in the certified shape, with solar-verify's exported spec

`published` is `Shape.published` with the postcondition read off solar-verify's export of
`Certified/counter/counter.sol` (`/// @custom:ensures x == old(x) + d` on `inc`; `get` has no
spec), `Shapes.bundlePost Headline.spec Headline.ctxOf Headline.step`, in place of the Lean
restatement `Shapes.specPost cspec`: the meets obligation is `Headline.holds_source` (the
exported spec of SolidCore's checked `Counter` on `scopeEvery`, which covers every valid call)
through `Shapes.meets_of_bundle`. The certify driver states the same postcondition over the bundle
it exports in its own run; the kernel accepts this proof there only if the two bundles agree.

Non-vacuity (`post_rejects`, `allowed_rejects`): the specification rejects a result of a valid
call (`inc(1)` from the empty storage succeeding with slot 0 left at 0), and the allowed statuses
reject a revert of a valid call (`inc(1)` with no value reverting with empty data, which is neither
the overflow's `Panic(0x11)` nor a call with value).
-/

namespace SolidCore.Refinement.Solar.Counter.ShapeExport

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide SolidCore.Refinement.Evm
open SolidCore.Refinement.Solar.Counter.Final SolidCore.Refinement.Solar.Counter.ShapeSpec
open SolidCore.Refinement.Solar.Counter.Headline
open EthLib.Base

/-- The published shape with solar-verify's exported spec as the postcondition. -/
theorem published : ∃ c, contract? = .ok c ∧
    Shapes.Certified (solidCore fuel) c CounterRun.code cspec.Calls allowed
      (Shapes.bundlePost Headline.spec Headline.ctxOf Headline.step) gasBound := by
  obtain ⟨c, hc, h⟩ := Shape.published
  exact ⟨c, hc, { h with meets := Shapes.meets_of_bundle (fun _ h => calls_every h) (holds_source hc) }⟩

/-- `inc(1)` with no value from the empty storage. -/
def incCall : Call := { callOf incSelector [1#256] with storage := [] }

theorem incCall_valid : cspec.Calls incCall := by
  refine ⟨incSpec, by simp [cspec, SolidCore.Refinement.Solar.Counter.Final.spec], [1],
    .cons (by decide) .nil, 0, by decide, [], ?_⟩
  rw [inc_call 1 0 (by decide) []]
  rfl

/-- **The specification is not vacuous**: it rejects `inc(1)` succeeding with slot 0 left at 0. -/
theorem post_rejects : ∃ call obs, cspec.Calls call ∧
    ¬ Shapes.bundlePost Headline.spec Headline.ctxOf Headline.step call obs := by
  refine ⟨incCall, { expectedAt [] 1#256 with storage := slotValue [] }, incCall_valid, ?_⟩
  intro h
  let pre : SolidCore.Spec.State := ⟨slotValue [], SolidCore.Spec.Ghost.zero, 0⟩
  have hne : Headline.spec.spec.specs ≠ [] := by
    simp [Headline.spec, SolidCore.Spec.Export.Counter.Counter]
  have hfs := List.head_mem hne
  have hpre : SolidCore.Spec.Pre Headline.spec (Headline.spec.spec.specs.head hne)
      (Headline.ctxOf incCall) pre incCall [1] := by
    refine ⟨⟨?_, ?_, ?_⟩, rfl, by simp [pre, Headline.ctxOf], ?_, ?_⟩
    · have := size_callOf 1#256
      simp only [incCall] at this ⊢
      omega
    · change SolidCore.Spec.selectorOf
        ({ calldata := (callOf incSelector [1#256]).calldata, callvalue := 0, storage := [] } : Call) = _
      have := spec_selectorOf_append incSelector (by decide) (wordsBytes [1#256]) 0 []
      rw [← calldata_inc] at this
      rw [this]
      simp [Headline.spec, SolidCore.Spec.Export.Counter.Counter, incSelector]
    · show SolidCore.Spec.decodeWords _ (SolidCore.Spec.words
        (((callOf incSelector [1#256]).calldata.data.toList.map (·.toNat)).drop 4)) = _
      rw [words_inc]
      simp [Headline.spec, SolidCore.Spec.Export.Counter.Counter, SolidCore.Spec.decodeWords,
        SolidCore.Spec.Ty.ofWord, bind, pure]
    · simp [SolidCore.Spec.Bundle.satAll, Headline.spec, SolidCore.Spec.Export.Counter.Counter]
    · simp [SolidCore.Spec.Bundle.satAll, Headline.spec, SolidCore.Spec.Export.Counter.Counter]
  have hpost := h _ hfs [1] pre hpre
  have hok : (expectedAt [] 1#256).success = true := by simp [expectedAt, slotValue]
  obtain ⟨rets, -, hens, -⟩ := hpost.1 hok
  have := hens _ (List.mem_singleton_self _)
  simp [SolidCore.Spec.Bundle.sat, Headline.spec, SolidCore.Spec.Export.Counter.Counter,
    SolidCore.Spec.eval, SolidCore.Spec.slotOf, SolidCore.Spec.mkEnv, SolidCore.Spec.Env.cur,
    SolidCore.Spec.BinOp.apply, SolidCore.Spec.Ty.ofBits, SolidCore.Spec.toWord, pre,
    slotValue] at this

/-- **The allowed statuses are not vacuous**: `inc(1)` with no value reverting with empty data is
not allowed. -/
theorem allowed_rejects : ∃ call obs, cspec.Calls call ∧ obs.success = false ∧ ¬ allowed call obs := by
  refine ⟨incCall, { expectedAt [] 1#256 with success := false, output := [] },
    incCall_valid, rfl, ?_⟩
  intro h
  rcases h with h | h | ⟨h, -⟩
  · cases h
  · exact h rfl
  · have := congrArg List.length h
    simp only [SolidCore.Verify.panic, List.length_append, List.length_map, length_word, List.length_nil] at this
    omega

/-- Both non-vacuity witnesses, as the published statement asks for them. -/
theorem nonvacuous : (∃ call obs, cspec.Calls call ∧
      ¬ Shapes.bundlePost Headline.spec Headline.ctxOf Headline.step call obs) ∧
    (∃ call obs, cspec.Calls call ∧ obs.success = false ∧ ¬ allowed call obs) :=
  ⟨post_rejects, allowed_rejects⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.ShapeExport.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

/-- info: 'SolidCore.Refinement.Solar.Counter.ShapeExport.nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonvacuous

end SolidCore.Refinement.Solar.Counter.ShapeExport
