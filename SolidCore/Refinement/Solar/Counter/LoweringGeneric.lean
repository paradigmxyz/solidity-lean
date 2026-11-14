import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Solar.Counter.Lowering

/-!
# counter's source stage, from the generic source stage

`Counter.Lowering` proves the source stage of Counter

    contract Counter { uint256 x; function inc(uint256 d) external { x += d; }
      function get() external view returns (uint256) { return x; } }

for `inc` from empty storage, by symbolic execution of this one module. The generic source stage
`Generic.stage` gives more from one evaluation by the kernel: both functions, from any storage.

* `check_stage0`: `Generic.check` accepts solar's first lowered MIR module
  `SolarTV.Export.Counter.stage0` for `Counter.coreLit` and both functions, `allFns`
  (`decide +kernel`): for `inc`, the erased tree (read slot 0, add `d` with solar's overflow check,
  write slot 0) and the symbolic run agree, and for `get` (return slot 0) too.
* `loweringAt`: the stage on every call of `inc` or `get` on any argument words, no value, from any
  storage, under every oracle; `lowering_generic`: on `Counter.scope`, the statement of
  `Counter.lowering`.
* `check_rejects_bad`: the check rejects `badStage0` (`inc` storing `d + 1`).
* `checkValue_stage0`: `Generic.checkValue` accepts stage0 (`decide +kernel`): neither function
  is payable and stage0 reverts with empty output on a call of either with a value other than 0,
  so `loweringAtValue` is `loweringAt` at every value below `2 ^ 256` (`Generic.stageValue`).

No sorry, native_decide or bv_decide; the axioms are pinned below.
-/

namespace SolidCore.Refinement.Solar.Counter

open SolidCore.Refinement SolidCore.Refinement.Abi

/-- Both functions of Counter and their parameters. -/
def allFns : List Fn := [⟨incSelector, [(.uint 256)]⟩, ⟨getSelector, []⟩]

/-- Every call of `inc` or `get` on any argument words, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope allFns σ call

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for both functions. -/
theorem check_stage0 :
    Generic.check fuel 16 coreLit SolarTV.Export.Counter.stage0 allFns = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check rejects stage0 with `inc` storing `d + 1`. -/
theorem check_rejects_bad : Generic.check fuel 16 coreLit badStage0 allFns = false := by
  decide +kernel

/-- **The source stage of Counter from any storage, for both functions**, from the generic
source stage. -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      scopeAt := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stage o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0)

/-- **The source stage of Counter's `inc`**, from the generic source stage: the statement of
`Counter.lowering`. -/
theorem lowering_generic (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      scope := by
  refine SolarTV.Stage.mono (loweringAt o hc) ?_
  rintro _ ⟨fn, hfn, args, hlen, hargs, rfl⟩
  simp only [fns, List.mem_singleton] at hfn
  subst hfn
  exact ⟨[], _, List.mem_cons_self, args, hlen, hargs, rfl⟩

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: neither function is payable, and stage0 reverts with empty output on
a call of either with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue 16 coreLit SolarTV.Export.Counter.stage0 allFns = true := by
  decide +kernel

/-- **The source stage of Counter from any storage, for both functions, at every value**: every
call of `inc` or `get` on any argument words, with any value below `2 ^ 256`, under every
oracle. -/
theorem loweringAtValue (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) (SolarTV.MIR.Lowered.moduleSem o) c SolarTV.Export.Counter.stage0
      (fun call => ∃ σ v, Generic.fullScopeValue allFns σ v call) := by
  obtain ⟨hk, _, hemp⟩ := shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stageValue o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0) (by rw [hk]; exact checkValue_stage0)

/-- info: 'SolidCore.Refinement.Solar.Counter.loweringAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt

/-- info: 'SolidCore.Refinement.Solar.Counter.lowering_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_generic

/-- info: 'SolidCore.Refinement.Solar.Counter.checkValue_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_stage0

/-- info: 'SolidCore.Refinement.Solar.Counter.loweringAtValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAtValue

end SolidCore.Refinement.Solar.Counter
