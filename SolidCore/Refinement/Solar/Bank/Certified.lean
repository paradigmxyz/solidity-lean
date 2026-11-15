import SolidCore.Refinement.Solar.Bank.Lowering
import SolidCore.Refinement.Solar.Bank.Assembly
import SolidCore.Refinement.Solar.Hex
import bank.gen.Bank.Manifest
import SolidCore.Refinement.Keccak.TwoWords

/-!
# bank: SolidCore to solar's bytecode, through every stage

The end-to-end translation of `Bank` (Lowering.lean has the contract), chaining with
`Stage.trans`:

1. the source stage, SolidCore's checked `Bank` to solar's first lowered MIR stage0
   (`lowering`, `loweringValue`), under every oracle whose caller is SolidCore's
   `callerAddress` and whose Keccak-256 of two words is SolidCore's (`Generic.SourceEnvOk`);
2. solar-tv's backend stages from stage0 to the final EVM IR, and the assembly stage to the
   runtime bytecode (Assembly.lean, `backend`), under every oracle whose caller and hash are
   EthLib's (`Assemble.OracleOk`).

An oracle with EthLib's caller has SolidCore's caller (`callerOk_of`). SolidCore hashes with
evmyul's Keccak-256 and EthLib with its own: `certified` and `certifiedValue` take, as their one
hypothesis beyond `OracleOk`, that they agree on the 64 bytes of two words (`EthKeccakAgree`,
the inputs a mapping's slot hashes), and `certified'` and `certifiedValue'` discharge it:
Keccak/Agree.lean proves the two implementations equal on every 64-byte message (same padding,
same Keccak-f[1600] round by round, same squeeze), and Keccak/TwoWords.lean reads that as
`EthKeccakAgree` (`ethKeccakAgree`). `certified` holds for every call of `deposit`, `depositFor` and `balanceOf` on any argument words,
from any storage, with no value, and `certifiedValue` with any value.

`certifiedManifest` binds both to the export's manifest (gen/…/Manifest.lean): the source's path
and sha256, the compiler's version and commit, its arguments, optimization and EVM version, the
bytecode's sha256 and hex, that the hex is the lowercase hex of the bytes the stages run
(`manifest_hex`, by the kernel's unfolding) and decodes to them (`bytecode_of_manifest`), and
the stages under `EthKeccakAgree`, as one conjunction. `mutant_hex_rejected`: a one-byte mutant's hex does not
decode to those bytes. The sha256s are of the files, checked outside the kernel (solar's
certify.sh; the source's, each stage's and the bytecode's match the files at solar c8ea95b8f).
`certifiedManifest'` is the same conjunction with `EthKeccakAgree` discharged (`ethKeccakAgree`).

No sorry, native_decide or bv_decide: the theorems depend on propext, Classical.choice and
Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar.Bank

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

/-- EthLib's Keccak-256 of the 64 bytes of two words is SolidCore's mapping-slot hash of them. -/
def EthKeccakAgree : Prop :=
  ∀ a b, a < 2 ^ 256 → b < 2 ^ 256 →
    (EthLib.Execution.Evm.keccak
      ⟨((Generic.wordBytes a ++ Generic.wordBytes b).map UInt8.ofBitVec).toArray⟩).toNat =
      Generic.solHash a b % 2 ^ 256

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

/-- An oracle with EthLib's caller and hash is one the source stage takes, when EthLib's and
SolidCore's Keccak-256 agree on two words. -/
theorem sourceEnvOk_of (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (hk : EthKeccakAgree) : Generic.SourceEnvOk o :=
  ⟨callerOk_of o ho, fun a b ha hb => by rw [ho.2]; exact hk a b ha hb⟩

/-- **Bank from SolidCore to solar's bytecode**: every result SolidCore's `Bank` gives on a
call of `deposit`, `depositFor` and `balanceOf` on any argument words, no value, from any storage, the bytecode gives under
EthLib, for every oracle with EthLib's caller and hash. -/
theorem certified (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o) (hk : EthKeccakAgree)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) :=
  (lowering o (sourceEnvOk_of o ho hk) hc).trans (backend o ho _)

/-- **Bank from SolidCore to solar's bytecode at every value**. -/
theorem certifiedValue (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (hk : EthKeccakAgree) {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  (loweringValue o (sourceEnvOk_of o ho hk) hc).trans (backend o ho _)

open SolarTV.Export.Bank Hex in
set_option maxRecDepth 100000 in
/-- The manifest's hex is the lowercase hex of the bytes the stages run. -/
theorem manifest_hex : Manifest.bytecodeHex = String.ofList (hexChars bytecode) := by rfl

open SolarTV.Export.Bank Hex in
set_option maxRecDepth 100000 in
/-- The bytes the stages run are the manifest's hex, which --emit=bin-runtime printed. -/
theorem bytecode_of_manifest : hexBytes (codes Manifest.bytecodeHex) = some bytecode := by
  rw [manifest_hex, codes, String.toList_ofList]
  -- The instance is spelled out: with EvmYul in scope, instance search finds EvmYul's
  -- `Stack.instDecidableEq` for `List Nat`.
  exact @of_decide_eq_true _
    (@Option.instDecidableEq _ (@instDecidableEqList _ instDecidableEqNat) _ _) (by decide +kernel)

open SolarTV.Export.Bank Hex in
set_option maxRecDepth 100000 in
/-- A one-byte mutant's hex (the first byte, CALLVALUE, as ORIGIN) does not decode to the bytes
the stages run: the link fails by mismatch. -/
theorem mutant_hex_rejected :
    hexBytes ((hexChars (bytecode.set 0 0x32)).map Char.toNat) ≠ some bytecode := by
  exact @of_decide_eq_false (hexBytes ((hexChars (bytecode.set 0 0x32)).map Char.toNat) = some bytecode)
    (@Option.instDecidableEq _ (@instDecidableEqList _ instDecidableEqNat) _ _) (by decide +kernel)

open SolarTV.Export.Bank Hex in
/-- **The certified translation of bank**, bound to what it was compiled from and by: the source
(path and sha256), its arguments
(-Ogas, osaka), the bytecode with its sha256 and hex, the bytes the stages run as that bytecode,
and the stage from SolidCore's checked `Bank` to those bytes, with no value and with any value,
on every call of `deposit`, `depositFor` and `balanceOf` from any storage, under every oracle
with EthLib's caller and hash, given that EthLib's and SolidCore's Keccak-256 agree on the 64 bytes
of two words (`EthKeccakAgree`, kept explicit here; `certifiedManifest'` discharges it with
`ethKeccakAgree`). -/
theorem certifiedManifest (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (hk : EthKeccakAgree) {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Manifest.sources = [("Certified/bank/bank.sol",
      "2a29919999674ac221097e3f50ed43bcddf094d19a08da5f5c9704a0dd099d03")] ∧
    Manifest.arguments = ["Certified/bank/bank.sol", "-Ogas", "--evm-version", "osaka",
      "--emit=bin-runtime", "-Zemit-lean-stages=Certified/bank/gen"] ∧
    Manifest.optimization = "Gas" ∧ Manifest.evmVersion = "osaka" ∧
    Manifest.bytecodeSha256 = "bff0578068ce4ab4a041f226e4e960c13d358c8b430718fefe9ce3a22d760543" ∧
    Manifest.bytecodeHex = bytecodeHex ∧
    Manifest.bytecodeHex = String.ofList (hexChars bytecode) ∧
    hexBytes (codes Manifest.bytecodeHex) = some bytecode ∧
    code = ⟨(bytecode.map UInt8.ofNat).toArray⟩ ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, manifest_hex, bytecode_of_manifest, rfl, certified o ho hk hc,
    certifiedValue o ho hk hc⟩

/-- EthLib's and SolidCore's Keccak-256 agree on the 64 bytes of two words (for every pair of
numbers, not only words). -/
theorem ethKeccakAgree : EthKeccakAgree :=
  fun a b _ _ => Keccak.ethKeccak_twoWords a b

/-- **Bank from SolidCore to solar's bytecode**, with no Keccak hypothesis: every result
SolidCore's `Bank` gives on a call of `deposit`, `depositFor` and `balanceOf` on any argument
words, no value, from any storage, the bytecode gives under EthLib, for every oracle with EthLib's
caller and hash. -/
theorem certified' (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) :=
  certified o ho ethKeccakAgree hc

/-- **Bank from SolidCore to solar's bytecode at every value**, with no Keccak hypothesis. -/
theorem certifiedValue' (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  certifiedValue o ho ethKeccakAgree hc

open SolarTV.Export.Bank Hex in
/-- **The certified translation of bank, with no Keccak hypothesis**, bound to its manifest:
`certifiedManifest`'s conjunction with `EthKeccakAgree` discharged by `ethKeccakAgree` (EthLib's
and evmyul's Keccak-256 proved equal on every 64-byte message). -/
theorem certifiedManifest' (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Manifest.sources = [("Certified/bank/bank.sol",
      "2a29919999674ac221097e3f50ed43bcddf094d19a08da5f5c9704a0dd099d03")] ∧
    Manifest.arguments = ["Certified/bank/bank.sol", "-Ogas", "--evm-version", "osaka",
      "--emit=bin-runtime", "-Zemit-lean-stages=Certified/bank/gen"] ∧
    Manifest.optimization = "Gas" ∧ Manifest.evmVersion = "osaka" ∧
    Manifest.bytecodeSha256 = "bff0578068ce4ab4a041f226e4e960c13d358c8b430718fefe9ce3a22d760543" ∧
    Manifest.bytecodeHex = bytecodeHex ∧
    Manifest.bytecodeHex = String.ofList (hexChars bytecode) ∧
    hexBytes (codes Manifest.bytecodeHex) = some bytecode ∧
    code = ⟨(bytecode.map UInt8.ofNat).toArray⟩ ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call) ∧
    Stage (solidCore fuel) ethLib c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  certifiedManifest o ho ethKeccakAgree hc

/-- info: 'SolidCore.Refinement.Solar.Bank.callerOk_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms callerOk_of

/-- info: 'SolidCore.Refinement.Solar.Bank.ethKeccakAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ethKeccakAgree

/-- info: 'SolidCore.Refinement.Solar.Bank.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.Bank.certifiedValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedValue

/-- info: 'SolidCore.Refinement.Solar.Bank.manifest_hex' does not depend on any axioms -/
#guard_msgs in
#print axioms manifest_hex

/-- info: 'SolidCore.Refinement.Solar.Bank.bytecode_of_manifest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bytecode_of_manifest

/-- info: 'SolidCore.Refinement.Solar.Bank.certifiedManifest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedManifest

/-- info: 'SolidCore.Refinement.Solar.Bank.certified'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified'

/-- info: 'SolidCore.Refinement.Solar.Bank.certifiedValue'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedValue'

/-- info: 'SolidCore.Refinement.Solar.Bank.certifiedManifest'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certifiedManifest'

end SolidCore.Refinement.Solar.Bank
