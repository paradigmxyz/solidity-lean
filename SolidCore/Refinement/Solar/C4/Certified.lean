import SolidCore.Refinement.Solar.C4.Lowering
import SolidCore.Refinement.Solar.C4.LoweringGeneric
import SolidCore.Refinement.Solar.C4.Assembly
import c4.Proofs.Stages
import c4.gen.Main.Manifest

/-!
# c4: SolidCore to solar's bytecode, through every stage

The end-to-end certified translation of the corpus contract c4 (scripts/refinement/corpus/c4.sol),

    contract Main { uint8 v; uint8 w = 7;
      function add(uint8 x) external returns (uint8) { v += x; w ^= x; return v; } }

by solar 7817979b with -Zcheck-analyses=false (default -Ogas, osaka), chaining with Stage.trans:

1. the source stage, SolidCore's checked Main to solar's first lowered MIR stage0
   (C4.lowering from the deployed storage, C4.loweringAt from any storage that writes slot 0;
   every call of add on any argument word, clean or dirty, no value, every oracle);
2. the backend stages of solar's solar-tv/milestone/c4, stage0 → mir1 (place-reads) → mir2
   (evm-inst-schedule) → sched (stack-schedule) → evm1 … evm5 (cfg-simplify-early,
   compact-pushes, share-reverts, terminal-dedup, cfg-simplify-early), each a kernel-checked
   symbolic run on every call with any call data, value and storage
   (SolarTV.Milestone.C4.c4_mir_to_evmir);
3. the assembly stage, evm5 to the 107 bytes of runtime bytecode, by the generic assembler check
   (Assembly.lean, stageAll from Assemble.stage_of_check_all).

The backend and assembly stages hold on every call, so the source stages at every value
(C4.lowering_value, C4.loweringAt_value in LoweringGeneric.lean, where SolidCore reverts a call
with a nonzero value and the MIR takes its paid branch) compose with them too:
certified_deployed_value and certified_at_value are certified_deployed and certified_at on calls
with any value below 2 ^ 256.

All three use the same exported modules (c4.gen.Main), so the stages compose by definition.
The bytes the assembly stage reaches (C4.code, the export's Bytecode.lean) are Corpus.C4.code,
the bytecode the specification and the corpus refinement speak of (code_eq, by the kernel).
The export's manifest (c4.gen.Main.Manifest) records the source's sha256, the compiler's version
and commit, its arguments, and the bytecode with its sha256; certified states them, and that the
bytes the stages run are the manifest's hex. solar's certify.sh checks the hashes against the
files (the source, each stage, the bytecode), outside the kernel.

* certified_deployed, certified_at: the stage from SolidCore to Corpus.C4.code on Verify.C4.scope
  (from the deployed storage) and on Verify.C4.scopeAt (any storage that writes slot 0).
* satisfies_at: Verify.C4's specification from any storage (postAt) holds of the bytecode, carried
  through these stages (Satisfies.of_stage), not through the bytecode's direct symbolic run.
* certified: all of it bound to the manifest.

No sorry, native_decide or bv_decide: the theorems depend on propext, Classical.choice and
Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.C4

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity SolarTV.Export.Main

/-- The value of a lowercase hex digit's ASCII code. -/
def hexDigit (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- The bytes a string of lowercase hex digits spells, from its ASCII codes. -/
def hexBytes : List Nat → Option (List Nat)
  | [] => some []
  | a :: b :: rest =>
    match hexDigit a, hexDigit b, hexBytes rest with
    | some x, some y, some r => some ((16 * x + y) :: r)
    | _, _, _ => none
  | [_] => none

/-- The ASCII codes of a string. -/
def codes (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)

set_option maxRecDepth 100000 in
/-- The bytes the stages run are the manifest's hex, which --emit=bin-runtime printed. -/
theorem bytecode_of_manifest : hexBytes (codes Manifest.bytecodeHex) = some bytecode := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The export's bytecode is the corpus's: the bytes the specification speaks of. -/
theorem code_eq : code = Corpus.C4.code := by
  decide +kernel

/-- The backend: solar-tv's stages from stage0 to evm5, then the assembly stage to the bytecode. -/
theorem backend (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    Stage (SolarTV.MIR.Lowered.moduleSem o) ethLib stage0 Corpus.C4.code scope :=
  code_eq ▸ SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    ((SolarTV.Milestone.C4.c4_mir_to_evmir o).mono fun _ _ => trivial) (stageAll o scope)

/-- **c4 from SolidCore to solar's bytecode**, from the deployed storage: every result
SolidCore's Main gives on a call of add on any argument word, no value, from the storage its
constructor leaves (slot 0 = 7 * 256), the bytecode gives under EthLib, for every oracle. -/
theorem certified_deployed (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code Verify.C4.scope :=
  (lowering o hc).trans (backend o _)

/-- **c4 from SolidCore to solar's bytecode**, from any storage that writes slot 0. -/
theorem certified_at (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code Verify.C4.scopeAt :=
  (loweringAt o hc).trans (backend o _)

/-- **c4 from SolidCore to solar's bytecode at every value**, from the deployed storage: every
result SolidCore's Main gives on a call of add on any argument word, with any value below 2 ^ 256,
from the storage its constructor leaves, the bytecode gives under EthLib, for every oracle. -/
theorem certified_deployed_value (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code
      (fun call => ∃ v, Generic.fullScopeValue Corpus.C4.fns Verify.C4.deployed v call) :=
  (lowering_value o hc).trans (backend o _)

/-- **c4 from SolidCore to solar's bytecode at every value**, from any storage that writes
slot 0. -/
theorem certified_at_value (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code scopeAtValue :=
  (loweringAt_value o hc).trans (backend o _)

/-- **c4's specification on solar's bytecode through every stage**: Verify.C4.postAt, from any
storage that writes slot 0, carried from SolidCore by certified_at. -/
theorem satisfies_at (o : SolarTV.Machine.Oracle) :
    Satisfies ethLib Corpus.C4.code Verify.C4.scopeAt Verify.C4.pre Verify.C4.postAt := by
  obtain ⟨c, hc, hspec⟩ := Verify.C4.satisfiesAt
  exact SolidCore.Refinement.Satisfies.of_stage hspec (certified_at o hc)

/-- **The certified translation of c4**, bound to what it was compiled from and by: the source
(path and sha256), its arguments
(-Zcheck-analyses=false, -Ogas, osaka), the bytecode with its sha256 and hex, the bytes the stages run
as that bytecode, and the stage from SolidCore's checked Main to those bytes, from the deployed
storage and from any storage that writes slot 0, with no value and with any value, under every
oracle, with the specification it carries. -/
theorem certified (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : Corpus.C4.contract? = .ok c) :
    Manifest.sources = [("Certified/c4/c4.sol",
      "31c39cd4e9c5cba0f78aff3a986d69be40c5f68cdb36fbf05ad3d0a5e950e858")] ∧
    Manifest.arguments = ["Certified/c4/c4.sol", "-Zcheck-analyses=false",
      "--emit=bin-runtime", "-Zemit-lean-stages=Certified/c4/gen"] ∧
    Manifest.optimization = "Gas" ∧ Manifest.evmVersion = "osaka" ∧
    Manifest.bytecodeSha256 = "8a21bc207d9dd8be48d921a717eda3ecb7e5bfcb5397850bc3d64a29037fac47" ∧
    Manifest.bytecodeHex = bytecodeHex ∧ hexBytes (codes Manifest.bytecodeHex) = some bytecode ∧
    Corpus.C4.code = ⟨(bytecode.map UInt8.ofNat).toArray⟩ ∧
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code Verify.C4.scope ∧
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code Verify.C4.scopeAt ∧
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code
      (fun call => ∃ v, Generic.fullScopeValue Corpus.C4.fns Verify.C4.deployed v call) ∧
    Stage (solidCore Corpus.C4.fuel) ethLib c Corpus.C4.code scopeAtValue ∧
    Satisfies ethLib Corpus.C4.code Verify.C4.scopeAt Verify.C4.pre Verify.C4.postAt :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, bytecode_of_manifest, code_eq.symm, certified_deployed o hc,
    certified_at o hc, certified_deployed_value o hc, certified_at_value o hc, satisfies_at o⟩

/-- info: 'SolidCore.Refinement.Solar.C4.code_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms code_eq

/-- info: 'SolidCore.Refinement.Solar.C4.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

/-- info: 'SolidCore.Refinement.Solar.C4.certified_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_deployed

/-- info: 'SolidCore.Refinement.Solar.C4.certified_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_at

/-- info: 'SolidCore.Refinement.Solar.C4.certified_deployed_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_deployed_value

/-- info: 'SolidCore.Refinement.Solar.C4.certified_at_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_at_value

/-- info: 'SolidCore.Refinement.Solar.C4.satisfies_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms satisfies_at

/-- info: 'SolidCore.Refinement.Solar.C4.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

end SolidCore.Refinement.Solar.C4
