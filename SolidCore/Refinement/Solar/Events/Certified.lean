import SolidCore.Refinement.Solar.Events.Lowering
import SolidCore.Refinement.Solar.Events.Assembly
import SolidCore.Refinement.Solar.Hex
import events.gen.Events.Manifest

/-!
# events: SolidCore to solar's bytecode, through every stage

The end-to-end translation of `Events` (Lowering.lean has the contract), chaining with
`Stage.trans`:

1. the source stage, SolidCore's checked `Events` to solar's first lowered MIR stage0
   (`lowering`, `loweringValue`), under every oracle whose caller is SolidCore's
   `callerAddress` (`Generic.CallerOk`): `Events` hashes nothing at run time;
2. solar-tv's backend stages from stage0 to the final EVM IR, and the assembly stage to the
   runtime bytecode (Assembly.lean, `backend`), under every oracle whose caller and hash are
   EthLib's (`Assemble.OracleOk`).

An oracle with EthLib's caller has SolidCore's (`callerOk_of`), so `certified` holds under
`Assemble.OracleOk` alone, for every call of `transfer` on any argument words, from any
storage, with no value, and `certifiedValue` with any value.

`certifiedManifest` binds both to the export's manifest (gen/…/Manifest.lean): the source's path
and sha256, the compiler's version and commit, its arguments, optimization and EVM version, the
bytecode's sha256 and hex, that the hex is the lowercase hex of the bytes the stages run
(`manifest_hex`, by the kernel's unfolding) and decodes to them (`bytecode_of_manifest`), and
the stages as one conjunction. `mutant_hex_rejected`: a one-byte mutant's hex does not
decode to those bytes. The sha256s are of the files, checked outside the kernel (solar's
certify.sh; the source's, each stage's and the bytecode's match the files at solar c8ea95b8f).

No sorry, native_decide or bv_decide: the theorems depend on propext, Classical.choice and
Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.Events

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

/-- EthLib's caller is SolidCore's `callerAddress`, as a word. -/
theorem callerAddress_word :
    (SolidCore.Refinement.Target.address SolidCore.Refinement.callerAddress).toU256.toNat =
      Generic.callerWord := by
  decide +kernel

/-- An oracle with EthLib's caller has SolidCore's. -/
theorem callerOk_of (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o) : Generic.CallerOk o := by
  unfold Generic.CallerOk
  rw [ho.1]
  exact callerAddress_word

/-- **Events from SolidCore to solar's bytecode**: every result SolidCore's `Events` gives on a
call of `transfer` on any argument words, no value, from any storage, the bytecode gives under
EthLib, for every oracle with EthLib's caller and hash. -/
theorem certified (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) :=
  (lowering o (callerOk_of o ho) hc).trans (backend o ho _)

/-- **Events from SolidCore to solar's bytecode at every value**. -/
theorem certifiedValue (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  (loweringValue o (callerOk_of o ho) hc).trans (backend o ho _)

open SolarTV.Export.Events Hex in
set_option maxRecDepth 100000 in
/-- The manifest's hex is the lowercase hex of the bytes the stages run. -/
theorem manifest_hex : Manifest.bytecodeHex = String.ofList (hexChars bytecode) := by rfl

open SolarTV.Export.Events Hex in
set_option maxRecDepth 100000 in
/-- The bytes the stages run are the manifest's hex, which --emit=bin-runtime printed. -/
theorem bytecode_of_manifest : hexBytes (codes Manifest.bytecodeHex) = some bytecode := by
  rw [manifest_hex, codes, String.toList_ofList]
  -- The instance is spelled out: with EvmYul in scope, instance search finds EvmYul's
  -- `Stack.instDecidableEq` for `List Nat`.
  exact @of_decide_eq_true _
    (@Option.instDecidableEq _ (@instDecidableEqList _ instDecidableEqNat) _ _) (by decide +kernel)

open SolarTV.Export.Events Hex in
set_option maxRecDepth 100000 in
/-- A one-byte mutant's hex (the first byte, CALLVALUE, as ORIGIN) does not decode to the bytes
the stages run: the link fails by mismatch. -/
theorem mutant_hex_rejected :
    hexBytes ((hexChars (bytecode.set 0 0x32)).map Char.toNat) ≠ some bytecode := by
  exact @of_decide_eq_false (hexBytes ((hexChars (bytecode.set 0 0x32)).map Char.toNat) = some bytecode)
    (@Option.instDecidableEq _ (@instDecidableEqList _ instDecidableEqNat) _ _) (by decide +kernel)

open SolarTV.Export.Events Hex in
/-- **The certified translation of events**, bound to what it was compiled from and by: the
source (path and sha256), its arguments (-Ogas, osaka),
the bytecode with its sha256 and hex, the bytes the stages run as that bytecode, and the stage
from SolidCore's checked `Events` to those bytes, with no value and with any value, on every call
of `transfer` from any storage, under every oracle with EthLib's caller and hash. -/
theorem certifiedManifest (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Manifest.sources = [("Certified/events/events.sol",
      "c935cf243f303a252e4ee0bb10c9c75130eef92ca6c4a954830e67af9a939214")] ∧
    Manifest.arguments = ["Certified/events/events.sol", "-Ogas", "--evm-version", "osaka",
      "--emit=bin-runtime", "-Zemit-lean-stages=Certified/events/gen"] ∧
    Manifest.optimization = "Gas" ∧ Manifest.evmVersion = "osaka" ∧
    Manifest.bytecodeSha256 = "5ad38c8bca24e0ca8c4a5e95f1f07bf993aad9a02ac3bc0872fc41fab8a6298b" ∧
    Manifest.bytecodeHex = bytecodeHex ∧
    Manifest.bytecodeHex = String.ofList (hexChars bytecode) ∧
    hexBytes (codes Manifest.bytecodeHex) = some bytecode ∧
    code = ⟨(bytecode.map UInt8.ofNat).toArray⟩ ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, manifest_hex, bytecode_of_manifest, rfl, certified o ho hc,
    certifiedValue o ho hc⟩

/-- info: 'SolidCore.Refinement.Solar.Events.callerOk_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms callerOk_of

/-- info: 'SolidCore.Refinement.Solar.Events.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.Events.certifiedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedValue

/-- info: 'SolidCore.Refinement.Solar.Events.manifest_hex' does not depend on any axioms -/
#guard_msgs in
#print axioms manifest_hex

/-- info: 'SolidCore.Refinement.Solar.Events.bytecode_of_manifest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytecode_of_manifest

/-- info: 'SolidCore.Refinement.Solar.Events.certifiedManifest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedManifest

end SolidCore.Refinement.Solar.Events
