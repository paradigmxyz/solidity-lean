import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Solar.Lowering

/-!
# w5's source stage as an instance of the generic source stage

`Solar.Lowering` proves the source stage of w5 (solar's w1, `f(a, b)` returning `a + b`) by
symbolic execution of this one module. Here the same stages follow from the generic source stage
`Generic.stage` and one evaluation by the kernel:

* `check_stage0`: `Generic.check` accepts solar's first lowered MIR module
  `SolarTV.Export.Main.stage0` for SolidCore's core `Corpus.W5.coreLit` and `Corpus.W5.fns`, by
  `decide +kernel`: the erased tree of `f` and the symbolic run of the module on `f`'s selector
  agree in normal form.
* `loweringAt_generic`: the stage on `Verify.W5.scopeAt` (every call of `f` on any two words, no
  value, any storage), under every oracle; `lowering_generic` on `Verify.W5.scope` (empty
  storage), the statements of `Solar.W1.loweringAt` and `Solar.W1.lowering`.
* `check_rejects_bad`: the check rejects `badStage0`, stage0 with the addition compiled as a
  subtraction.
* `checkValue_stage0`: `Generic.checkValue` accepts stage0 (`decide +kernel`): `f` is not
  payable and stage0 reverts with empty output on a call of it with a value other than 0, so
  `loweringAt_value` and `lowering_value` are the two stages above at every value below
  `2 ^ 256` (`Generic.stageValue`).

No sorry, native_decide or bv_decide: `decide +kernel` is the kernel's evaluation, and the
theorems depend on propext, Classical.choice and Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.W1

open SolidCore.Refinement SolidCore.Refinement.Abi

/-- The interpreter fuel of the symbolic run of the module: blocks along each path. -/
def mirFuel : Nat := 16

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for w5's `f`. -/
theorem check_stage0 :
    Generic.check Corpus.W5.fuel mirFuel Corpus.W5.coreLit SolarTV.Export.Main.stage0
      Corpus.W5.fns = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check rejects stage0 with `a - b` for `a + b`. -/
theorem check_rejects_bad :
    Generic.check Corpus.W5.fuel mirFuel Corpus.W5.coreLit badStage0 Corpus.W5.fns = false := by
  decide +kernel

/-- **The source stage of w5 from any storage, from the generic source stage.** -/
theorem loweringAt_generic (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.W5.scopeAt := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W5.shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stage o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0)

/-- **The source stage of w5, from the generic source stage**: every call of `f` with no value
and empty storage. -/
theorem lowering_generic (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.W5.scope :=
  SolarTV.Stage.mono (loweringAt_generic o hc) fun _ h => ⟨[], h⟩

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: `f` is not payable, and stage0 reverts with empty output on a call of
it with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel Corpus.W5.coreLit SolarTV.Export.Main.stage0 Corpus.W5.fns =
      true := by
  decide +kernel

/-- **The source stage of w5 from any storage, at every value**: every call of `f` on any two
words, with any value below `2 ^ 256`, under every oracle. -/
theorem loweringAt_value (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ σ v, Generic.fullScopeValue Corpus.W5.fns σ v call) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W5.shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stageValue o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- **The source stage of w5 at every value**: every call of `f` with any value below `2 ^ 256`
and empty storage. -/
theorem lowering_value (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W5.contract? = .ok c) :
    Stage (solidCore Corpus.W5.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ v, Generic.fullScopeValue Corpus.W5.fns [] v call) :=
  SolarTV.Stage.mono (loweringAt_value o hc) fun _ ⟨v, h⟩ => ⟨[], v, h⟩

/-- info: 'SolidCore.Refinement.Solar.W1.loweringAt_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt_generic

/-- info: 'SolidCore.Refinement.Solar.W1.lowering_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_generic

/-- info: 'SolidCore.Refinement.Solar.W1.checkValue_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_stage0

/-- info: 'SolidCore.Refinement.Solar.W1.loweringAt_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt_value

/-- info: 'SolidCore.Refinement.Solar.W1.lowering_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_value

end SolidCore.Refinement.Solar.W1
