import SolidCore.Refinement.Solar.Lowering
import SolidCore.Refinement.Spec
import W1Proofs.Stages
import gen.Main.Manifest

/-!
# The w5 milestone: solar's bytecode meets w5's verified specification, every stage proved

The contract (scripts/refinement/corpus/w5.sol; solar-tv/milestone/w1/w1.sol in solar's tree,
the same contract),

    contract Main { function f(uint256 a, uint256 b) external pure returns (uint256) {
      return a + b; } }

compiled by solar (compiler sources of commit 81dbc26c, -Ogas --evm-version osaka) to the 68
bytes of runtime bytecode code, whose sha256 is runtimeSha256. certified states, with no
hypothesis, that code meets w5's specification (Verify.W5: f(a, b) returns the word a + b when
it fits in 256 bits and otherwise reverts with Panic(0x11), logs nothing, and leaves storage
empty) on EthLib, and that code is the bytecode solar exported with its stages, as the
manifest records it. The specification is proved of SolidCore's checked contract with the
Loom VC generator (Verify.W5.satisfies) and carried to the bytecode through solar's actual
pipeline (bytecode_of_stages), every stage a theorem:

* source: SolidCore to the first lowered MIR, lower-abi and lower-dispatch included
  (lowering, SolidCore/Refinement/Solar/Lowering.lean);
* backend: the first lowered MIR through stack scheduling and the four EVM IR passes to the
  final EVM IR (SolarTV.Milestone.W1.w1_mir_to_evmir, solar-tv/milestone/w1/proofs);
* assembly: the final EVM IR to the bytecode on EthLib (stage, SolidCore/Refinement/Solar/W1.lean):
  Assemble.stage_of_check, proved once for every EVM IR program of the fragment and every code
  the checker accepts (SolidCore/Refinement/Solar/AssembleSim.lean), at check_ok, the kernel's
  evaluation of the checker on w1's final EVM IR and bytecode.

The stages hold under every oracle of SolarTV's semantics; the composition uses oracle, the
environment of EthLib's call.

## Scope

* Syntax: this one contract, a single external pure function of two uint256 parameters
  returning their checked sum. Nothing else is claimed for any other source: the certificate
  is translation validation of this compilation, and another source or compiler output fails
  the stage proofs (the procedures leave goals) or the artifact checks of
  scripts/refinement/w5-milestone.sh.
* Calls: one call (no call sequences) of f, selector 0x13d1aa2e, with well-formed call data,
  the selector followed by two words below 2^256 (68 bytes; Verify.W5.scope, Abi.fullScope).
  Short, long or otherwise malformed call data, other selectors, and nonzero call value are
  outside the scope; the stages say nothing about them.
* Call value: zero. Initial storage: empty, the storage SolidCore's constructor leaves
  (checked by the kernel, Corpus.W5.shape_eq); the bytecode reads no storage.
  certifiedAt widens this to any initial storage: on Verify.W5.scopeAt (every call of f with
  no value from any storage σ, which the call writes over the deployed one), code meets
  Verify.W5.postAt (the same result, with every slot of σ kept), through loweringAt,
  w1_mir_to_evmir and stageAt, each proved from any storage (EthLib's preState reads σ,
  getStorage_preState); stageAt is the same Assemble.stage_of_check at the same check_ok.
* Reverts: the overflow path, a revert with Panic(0x11) data, is in the scope and proved.
* Logs: none, proved (the specification states logs = []). External calls: none.
* EVM: EthLib at Fusaka (solar's --evm-version osaka), one message frame from 0x2000 to 0x1000
  with 10M gas (Statement.lean's Target.run). Gas is metered and checked on every step of the
  bytecode run, so the theorem includes that 10M gas suffices on every path. Proof fuel is
  separate: SolidCore runs with interpreter fuel Corpus.W5.fuel = 4096, SolarTV's MIR and EVM
  IR semantics are fuel-free (each run ends within a few blocks), and none of it is EVM gas.

## Unverified boundaries

* Source parsing into SolidCore: SolidCore's checked contract is Corpus.W5.contract?, the
  type checker on Source.W5.importedSourceUnit, which scripts/refinement/gen.sh produces from
  w5.sol with solidity-lean's front end. That front end, and that w5.sol is the source solar
  compiled (the check script compares the two files modulo comments and whitespace and
  compiles both), are outside the proof. The type checker's output on the parsed source is
  checked by the kernel.
* Artifact import: solar's stages enter Lean as text it writes (-Zemit-lean-stages, gen/Main);
  that the printed terms are the compiler's internal IR is not proved. The check script
  regenerates them with solar and compares them byte for byte, and checks that the bytecode
  literal is solar's --emit=bin-runtime output and its sha256.
* The semantics themselves (SolidCore, SolarTV's MIR and EVM IR, EthLib) are the trusted
  definitions the theorems are stated in.
-/

namespace SolidCore.Refinement.Solar.W1

open SolidCore.Refinement

/-- **The milestone.** solar's runtime bytecode for w5, which is the bytecode solar exported
with its stages (byte for byte, and as the hex and sha256 its manifest records for compiler
81dbc26c with -Ogas for osaka), meets w5's specification verified on SolidCore, under EthLib
on every call of the scope, through every stage of solar's pipeline. -/
theorem certified :
    bytes = SolarTV.Export.Main.bytecode ∧
    SolarTV.Export.Main.Manifest.bytecodeHex = runtimeHex ∧
    SolarTV.Export.Main.Manifest.bytecodeSha256 = runtimeSha256 ∧
    SolarTV.Export.Main.Manifest.compiler = "0.8.38+commit.3ca8f483.solar.0.3.0-dev" ∧
    SolarTV.Export.Main.Manifest.optimization = "Gas" ∧
    SolarTV.Export.Main.Manifest.evmVersion = "osaka" ∧
    Satisfies ethLib code Verify.W5.scope Verify.W5.pre Verify.W5.post := by
  refine ⟨bytes_exported, rfl, rfl, rfl, rfl, rfl, ?_⟩
  obtain ⟨c, hc, hspec⟩ := Verify.W5.satisfies
  exact bytecode_of_stages hspec (lowering oracle hc)
    ((SolarTV.Milestone.W1.w1_mir_to_evmir oracle).mono fun _ _ => trivial) (stage oracle)

/-- **The milestone from any storage.** The same bytecode meets w5's specification from any
storage (`Verify.W5.specAt`: on every call of f with no value from any storage `σ`, the result
of `post` with `σ` kept), under EthLib, through every stage of solar's pipeline, each proved on
every call from any storage. -/
theorem certifiedAt : Satisfies ethLib code Verify.W5.scopeAt Verify.W5.pre Verify.W5.postAt := by
  obtain ⟨c, hc, hspec⟩ := Verify.W5.satisfiesAt
  exact bytecode_of_stages hspec (loweringAt oracle hc)
    ((SolarTV.Milestone.W1.w1_mir_to_evmir oracle).mono fun _ _ => trivial) (stageAt oracle)

/-- The bytecode is the corpus's: solidity-lean's own compilation of w5.sol with solar -Ogas
(Corpus.W5.code, commit 9688f215) is the same 68 bytes. -/
theorem code_eq_corpus : code = Corpus.W5.code := rfl

/-- info: 'SolidCore.Refinement.Solar.W1.lowering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowering

/-- info: 'SolidCore.Refinement.Solar.W1.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.W1.certifiedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedAt

end SolidCore.Refinement.Solar.W1
