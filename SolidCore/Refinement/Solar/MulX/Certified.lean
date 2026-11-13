import SolidCore.Refinement.Solar.MulX.Lowering
import SolidCore.Refinement.Solar.MulX.Assembly
import mulx.Proofs.Stages
import mulx.gen.Main.Manifest
import SolidCore.Refinement.Solar.Hex

/-!
# mulx: SolidCore to solar's bytecode, through every stage

The end-to-end certified translation of the test contract scripts/refinement/mulx/mul.sol,

    contract Main { uint8 x8; uint16 y16 = 3; uint256 z;
      function m(uint8 a, uint16 b) external { x8 *= a; y16 *= b; }
      function n(uint8 a, uint16 b, uint256 c) external returns (uint256) {
        z = uint256(a) * b * c; return z; } }

by solar a8179dfc with -Zcheck-analyses=false (default -Ogas, osaka), chaining with
Stage.trans:

1. the source stage, SolidCore's checked Main to solar's first lowered MIR stage0
   (MulX.lowering from the deployed storage, MulX.loweringAt from any storage that writes
   slot 0; every call of m and n on any argument words, no value, every oracle);
2. the backend stages of solar's solar-tv/milestone/mulx, stage0 → mir1 (place-reads) → mir2
   (spell-width-tests) → mir3 (evm-inst-schedule) → sched (stack-schedule) → evm1 … evm8
   (cfg-simplify-early, compact-pushes, block-layout, terminal-dedup, cfg-simplify-early,
   block-layout, stack-reschedule, terminal-layout), each a kernel-checked symbolic run on
   every call with any call data, value and storage (SolarTV.Milestone.Mulx.mulx_mir_to_evmir);
3. the assembly stage, evm8 to the 186 bytes of runtime bytecode (Assembly.lean, stageAll).

The backend stages hold on every call, so the source stages at every value (MulX.loweringValue,
MulX.loweringAtValue) compose with them too: certified_deployed_value and certified_at_value
are certified_deployed and certified_at on calls with any value below 2 ^ 256.

All three use the same exported modules (mulx.gen.Main), so the stages compose by definition.
The export's manifest (mulx.gen.Main.Manifest) records the source's sha256, the compiler's
version and commit, its arguments, and the bytecode with its sha256; certified states them, and
that the bytes the stages run are the manifest's hex. solar's certify.sh checks the hashes
against the files (the source, each stage, the bytecode), outside the kernel.

No sorry, native_decide or bv_decide: the theorems depend on propext, Classical.choice and
Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.MulX

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
  rw [show Manifest.bytecodeHex = String.ofList (Hex.hexChars bytecode) from rfl, codes,
    Hex.toUTF8_toList_ofList]
  decide +kernel

/-- The backend: solar-tv's stages from stage0 to evm8, then the assembly stage. -/
theorem backend (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    Stage (SolarTV.MIR.Lowered.moduleSem o) ethLib stage0 code scope :=
  SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    ((SolarTV.Milestone.Mulx.mulx_mir_to_evmir o).mono fun _ _ => trivial) (stageAll o scope)

/-- **mulx from SolidCore to solar's bytecode**, from the deployed storage: every result
SolidCore's Main gives on a call of m or n on any argument words, no value, from the storage
its constructor leaves (slot 0 = 3 * 256), the bytecode gives under EthLib, for every oracle. -/
theorem certified_deployed (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fullScope fns deployed) :=
  (lowering o hc).trans (backend o _)

/-- **mulx from SolidCore to solar's bytecode**, from any storage that writes slot 0. -/
theorem certified_at (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code scopeAt :=
  (loweringAt o hc).trans (backend o _)

/-- **mulx from SolidCore to solar's bytecode at every value**, from the deployed storage: every
result SolidCore's Main gives on a call of m or n on any argument words, with any value below
2 ^ 256, from the storage its constructor leaves, the bytecode gives under EthLib, for every
oracle. -/
theorem certified_deployed_value (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code
      (fun call => ∃ v, Generic.fullScopeValue fns deployed v call) :=
  (loweringValue o hc).trans (backend o _)

/-- **mulx from SolidCore to solar's bytecode at every value**, from any storage that writes
slot 0. -/
theorem certified_at_value (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code scopeAtValue :=
  (loweringAtValue o hc).trans (backend o _)

/-- **The certified translation of mulx**, bound to what it was compiled from and by: the
source (path and sha256), solar's version with its commit a8179dfc, its arguments
(-Zcheck-analyses=false, -Ogas, osaka), the bytecode with its sha256, the bytes the stages run
as that bytecode, and the stage from SolidCore's checked Main to those bytes, from the deployed
storage and from any storage that writes slot 0, under every oracle. -/
theorem certified (o : SolarTV.Machine.Oracle) {c : TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    Manifest.sources = [("solar-tv/milestone/mulx/mulx.sol",
      "50ef03a3c5724105509c3ed40b7ee7d92ea43b5d48a67d0e6722b26806dd4980")] ∧
    Manifest.compiler = "0.8.38+commit.4a7d9ede.solar.0.3.0-dev" ∧
    Manifest.arguments = ["solar-tv/milestone/mulx/mulx.sol", "-Zcheck-analyses=false",
      "--emit=bin-runtime", "-Zemit-lean-stages=solar-tv/milestone/mulx/gen"] ∧
    Manifest.optimization = "Gas" ∧ Manifest.evmVersion = "osaka" ∧
    Manifest.bytecodeSha256 = "42ecdc71b09d339299d2b7ce61e121c77b141c5386eb9cbf18792a9ba9ca4cfe" ∧
    Manifest.bytecodeHex = bytecodeHex ∧ hexBytes (codes Manifest.bytecodeHex) = some bytecode ∧
    code = ⟨(bytecode.map UInt8.ofNat).toArray⟩ ∧
    Stage (solidCore fuel) ethLib c code (fullScope fns deployed) ∧
    Stage (solidCore fuel) ethLib c code scopeAt :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, bytecode_of_manifest, rfl, certified_deployed o hc,
    certified_at o hc⟩

/-- info: 'SolidCore.Refinement.Solar.MulX.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_deployed

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_at

/-- info: 'SolidCore.Refinement.Solar.MulX.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_deployed_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_deployed_value

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_at_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_at_value

end SolidCore.Refinement.Solar.MulX
