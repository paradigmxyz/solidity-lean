import SolidCore.Refinement.Generic.Value
import SolidCore.Verify.C4
import c4.gen.Main.Stage0

/-!
# c4's source stage, from the generic source stage

The corpus contract c4 (scripts/refinement/corpus/c4.sol),

    contract Main { uint8 v; uint8 w = 7;
      function add(uint8 x) external returns (uint8) { v += x; w ^= x; return v; } }

has a narrow parameter that solar's lower-abi cleans (a dirty word reverts), a checked `uint8`
addition, two `uint8` fields packed in slot 0 (`v` at byte 0, `w` at byte 1) written by
read-modify-write, a compound `^=`, and a constructor that leaves slot 0 = `7 * 256`.
`Solar.C4.lowering` proves its source stage from the deployed storage by symbolic execution of
this one module. The generic source stage gives it from one evaluation by the kernel, and from
any storage that writes slot 0 too:

* `check_stage0`: `Generic.check` accepts solar's first lowered MIR module
  `SolarTV.Export.Main.stage0` (c4.gen.Main.Stage0, solar's export) for `Verify.C4.coreLit` and
  `Corpus.C4.fns` (`decide +kernel`): the erased tree of `add` (the argument check, `v += x`
  with `uint256`'s overflow check and `uint8`'s cleanup, `w ^= x`, the packed reads and writes
  of slot 0) and the symbolic run of the module agree in canonical form.
* `lowering_generic`: the stage on `Verify.C4.scope` (every call of `add` on any argument word,
  no value, from the deployed storage), under every oracle: the statement of
  `Solar.C4.lowering`, from `Generic.stageDeployed`.
* `loweringAt_generic`: the stage on `Verify.C4.scopeAt` (from any storage that writes slot 0),
  from `Generic.stageAt`, with no hypothesis on the MIR run: `Solar.C4.loweringAt_of_runs`'s
  conclusion for solar's stage0.
* `check_rejects_bad`: the check rejects `badStage0`, stage0 with `w ^= x` compiled as
  `w |= x`.
* `checkValue_stage0`: `Generic.checkValue` accepts stage0 (`decide +kernel`): `add` is not
  payable and stage0 reverts with empty output on a call of it with a value other than 0, so
  `lowering_value` and `loweringAt_value` are the two stages above at every value below
  `2 ^ 256` (`Generic.stageDeployedValue`, `Generic.stageAtValue`).

The names of solar's stages (`SolarTV.Export.Main`) are those of w1's and w4's too, so this
module is built by `lake build SolidCoreSolarC4`, outside the library root.

No sorry, native_decide or bv_decide: `decide +kernel` is the kernel's evaluation, and the
theorems depend on propext, Classical.choice and Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.C4

open SolidCore.Refinement SolidCore.Refinement.Abi

/-- The interpreter fuel of the symbolic run of the module: blocks along each path. -/
def mirFuel : Nat := 16

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check accepts stage0 for c4's `add`. -/
theorem check_stage0 :
    Generic.check Corpus.C4.fuel mirFuel Verify.C4.coreLit SolarTV.Export.Main.stage0
      Corpus.C4.fns = true := by
  decide +kernel

/-- An instruction of stage0 with `xor` compiled as `or`. -/
def mutateInst : SolarTV.MIR.Lowered.Inst → SolarTV.MIR.Lowered.Inst
  | .pure dst .xor args => .pure dst .or args
  | i => i

/-- stage0 with `w ^= x` compiled as `w |= x`. -/
def badStage0 : SolarTV.MIR.Lowered.Module :=
  { SolarTV.Export.Main.stage0 with
    functions := SolarTV.Export.Main.stage0.functions.map fun f =>
      { f with blocks := f.blocks.map fun b => { b with insts := b.insts.map mutateInst } } }

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: the generic check rejects stage0 with `w |= x` for `w ^= x`. -/
theorem check_rejects_bad :
    Generic.check Corpus.C4.fuel mirFuel Verify.C4.coreLit badStage0 Corpus.C4.fns = false := by
  decide +kernel

/-- c4's checked contract has the core `Verify.C4.coreLit`, and its constructor leaves exactly
`Verify.C4.deployed`. -/
theorem deployed_of {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    c.core = Verify.C4.coreLit ∧ ∃ d, Wide.DeployedAt Corpus.C4.fuel c d Verify.C4.deployed := by
  obtain ⟨hk, _, hdep⟩ := Verify.C4.shape_of hc
  exact ⟨hk, Wide.deployedAt_of hdep⟩

/-- **The source stage of c4 from the deployed storage, from the generic source stage**: the
statement of `Solar.C4.lowering`. -/
theorem lowering_generic (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.C4.scope := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageDeployed o hd (by rw [hk]; exact check_stage0)

/-- **The source stage of c4 from any storage that writes slot 0, from the generic source
stage**: every call of `add` on any argument word, no value, under every oracle. -/
theorem loweringAt_generic (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 Verify.C4.scopeAt := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  refine SolarTV.Stage.mono (Generic.stageAt o hd (by rw [hk]; exact check_stage0)) ?_
  rintro call ⟨σ, ⟨kv, hkv, h0⟩, hs⟩
  refine ⟨σ, ?_, hs⟩
  intro kv' hkv'
  simp only [Verify.C4.deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

set_option maxRecDepth 100000 in
/-- The kernel's evaluation: `add` is not payable, and stage0 reverts with empty output on a call
of it with a value other than 0. -/
theorem checkValue_stage0 :
    Generic.checkValue mirFuel Verify.C4.coreLit SolarTV.Export.Main.stage0 Corpus.C4.fns =
      true := by
  decide +kernel

/-- **The source stage of c4 from the deployed storage, at every value**: every call of `add` on
any argument word, with any value below `2 ^ 256`, under every oracle. -/
theorem lowering_value (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0
      (fun call => ∃ v, Generic.fullScopeValue Corpus.C4.fns Verify.C4.deployed v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.stageDeployedValue o hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- The calls of `add` from any storage that writes slot 0, with any value. -/
def scopeAtValue : Call → Prop := fun call =>
  ∃ σ v, (∃ kv ∈ σ, kv.1 % 2 ^ 256 = 0) ∧ Generic.fullScopeValue Corpus.C4.fns σ v call

/-- **The source stage of c4 from any storage that writes slot 0, at every value**: every call
of `add` on any argument word, with any value below `2 ^ 256`, under every oracle. -/
theorem loweringAt_value (o : SolarTV.Machine.Oracle)
    {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.Main.stage0 scopeAtValue := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  refine SolarTV.Stage.mono (Generic.stageAtValue o hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)) ?_
  rintro call ⟨σ, v, ⟨kv, hkv, h0⟩, hs⟩
  refine ⟨σ, v, ?_, hs⟩
  intro kv' hkv'
  simp only [Verify.C4.deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

/-- info: 'SolidCore.Refinement.Solar.C4.check_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms check_stage0

/-- info: 'SolidCore.Refinement.Solar.C4.lowering_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_generic

/-- info: 'SolidCore.Refinement.Solar.C4.loweringAt_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt_generic

/-- info: 'SolidCore.Refinement.Solar.C4.checkValue_stage0' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkValue_stage0

/-- info: 'SolidCore.Refinement.Solar.C4.lowering_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering_value

/-- info: 'SolidCore.Refinement.Solar.C4.loweringAt_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweringAt_value

end SolidCore.Refinement.Solar.C4
