import SolidCore.Refinement.Generic.Value
import SolidCore.Refinement.Corpus.W4
import w4.gen.Main.Stage0

/-!
# w4's source stage, from the generic source stage

The milestone contract w4 (solar-tv/milestone/w4/w4.sol, the corpus's w4),

    contract Main { uint256 x; function set(uint256 v) external { x = v; } }

from SolidCore's checked contract (`Corpus.W4.contract?`, whose core the kernel checks is
`Corpus.W4.coreLit` and whose constructor leaves no storage) to the first lowered MIR module
solar compiles for it (`SolarTV.Export.Main.stage0` of solar-tv's `w4.gen.Main.Stage0`, after
`lower-evm-shaped`), in SolarTV's lowered MIR semantics under any oracle. Nothing here is
specific to w4 beyond one evaluation by the kernel:

* `check_stage0`: `Generic.check` accepts the module for `Corpus.W4.fns` (`decide +kernel`): the
  erased tree of `set` (write argument 0 to slot 0, return nothing) is the symbolic run's.
* `loweringAt`: the stage on every call of `set` on any word, no value, from any storage;
  `lowering`: on `fullScope Corpus.W4.fns []` (`Verify.W4.scope`), from empty storage.
* `checkValue_stage0`: `Generic.checkValue` accepts the module (`decide +kernel`): `set` is not
  payable and the module reverts with empty output on a call of it with a value other than 0,
  so `loweringAtValue` and `loweringValue` are the two stages above at every value below
  `2 ^ 256` (`Generic.stageValue`).

solar-tv's w4 and w1 modules both declare `SolarTV.Export.Main.stage0`, so this module cannot be
imported together with `Solar.Lowering`, and the library root leaves it out; build it on its own
(`lake build SolidCore.Refinement.Solar.W4Lowering`).

No sorry, native_decide or bv_decide; the axioms are pinned below.
-/

namespace SolidCore.Refinement.Solar.W4

open SolidCore.Refinement SolidCore.Refinement.Abi

/-- Every call of `set` on any argument word, with no value, from any storage. -/
def scopeAt : Call → Prop := fun call => ∃ σ, fullScope Corpus.W4.fns σ call

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts w4's first lowered MIR module. -/
theorem check_stage0 :
    Generic.check Corpus.W4.fuel 16 Corpus.W4.coreLit SolarTV.Export.Main.stage0
      Corpus.W4.fns = true := by
  decide +kernel

/-- **The source stage of w4 from any storage**, from the generic source stage. -/
theorem loweringAt (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W4.contract? = .ok c) :
    Stage (solidCore Corpus.W4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 scopeAt := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W4.shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stage o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0)

/-- **The source stage of w4**: every call of `set` with no value and empty storage. -/
theorem lowering (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.W4.contract? = .ok c) :
    Stage (solidCore Corpus.W4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 (fullScope Corpus.W4.fns []) :=
  SolarTV.Stage.mono (loweringAt o hc) fun _ h => ⟨[], h⟩

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: `set` is not payable, and the module reverts with empty output on a
call of it with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue 16 Corpus.W4.coreLit SolarTV.Export.Main.stage0 Corpus.W4.fns = true := by
  decide +kernel

/-- **The source stage of w4 from any storage, at every value**: every call of `set` on any
word, with any value below `2 ^ 256`, under every oracle. -/
theorem loweringAtValue (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W4.contract? = .ok c) :
    Stage (solidCore Corpus.W4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ σ v, Generic.fullScopeValue Corpus.W4.fns σ v call) := by
  obtain ⟨hk, _, hemp⟩ := Corpus.W4.shape_of hc
  obtain ⟨d, hd⟩ := Wide.deployed_of hemp
  exact Generic.stageValue o (Verify.deployedAt_of_deployed hd)
    (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- **The source stage of w4 at every value**: every call of `set` with any value below
`2 ^ 256` and empty storage. -/
theorem loweringValue (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.W4.contract? = .ok c) :
    Stage (solidCore Corpus.W4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ v, Generic.fullScopeValue Corpus.W4.fns [] v call) :=
  SolarTV.Stage.mono (loweringAtValue o hc) fun _ ⟨v, h⟩ => ⟨[], v, h⟩

/-- info: 'SolidCore.Refinement.Solar.W4.loweringAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt

/-- info: 'SolidCore.Refinement.Solar.W4.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.W4.checkValue_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_stage0

/-- info: 'SolidCore.Refinement.Solar.W4.loweringAtValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAtValue

/-- info: 'SolidCore.Refinement.Solar.W4.loweringValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringValue

end SolidCore.Refinement.Solar.W4
