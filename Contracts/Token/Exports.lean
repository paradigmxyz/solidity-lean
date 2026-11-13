import Contracts.Token.EndToEnd
import Contracts.Token.Spec.Export
import Verify.Final

/-!
# Token's exports, by name

The Lean targets the exporters write for Token, under one name each, as the certify driver names
them for every contract:

* \`code\`: solar's runtime bytecode (Certified/verify_token, \`VerifyTokenAsm.code\`), and \`manifest\`
  the exporter's manifest of it (\`manifest_hex\`: its hex is the bytes'; \`export_bound\`: the spec
  export names the same SHA-256);
* \`spec\`: solar-verify's \`--emit-lean-spec\` export of scripts/verify/Token.sol
  (Contracts/Token/Spec/Export.lean, \`Token_wf\` checked by the kernel);
* \`contract\`: SolidCore's checked Token (\`contract_eq\`), \`fuel\` its source stage's fuel;
* \`scope\`: the calls the end-to-end theorem covers, \`transfer\` and \`burn\` in solar-verify's binding
  scope (\`spec_holds_of_bytecode\`);
* \`ctxOf\`: the call context of SolidCore's and EthLib's interface; \`step\`: the ghost \`sumBalances\`
  as the source's ghost updates write it (\`mint\` adds its amount, \`burn\` takes it away).
-/

namespace Contracts.Token

open SolidCore.Refinement SolidCore.Verify.VC SolidCore.Verify.VC.Token

/-- solar's runtime bytecode for Token. -/
abbrev code : ByteArray := SolidCore.Refinement.Solar.VerifyTokenAsm.code

/-- solar-verify's exported spec of Token. -/
abbrev spec : SolidCore.Spec.Bundle := SolidCore.Spec.Export.Token.Token

/-- The exporter's manifest of the bytecode. -/
def manifest : SolidCore.Refinement.Final.Manifest where
  contract := "Token"
  sourceSha256 := (SolarTV.Export.Token.Manifest.sources.headD ("", "")).2
  compilerCommit := SolarTV.Export.Token.Manifest.compiler
  options := SolarTV.Export.Token.Manifest.arguments
  runtimeHex := SolarTV.Export.Token.Manifest.bytecodeHex
  runtimeSha256 := SolarTV.Export.Token.Manifest.bytecodeSha256

/-- The spec export names the bytecode of the manifest. -/
theorem export_bound : SolidCore.Spec.Export.Token.manifest.bytecodeSha256 = manifest.runtimeSha256 := by
  decide +kernel

/-- SolidCore's checked Token. -/
noncomputable def contract : SolidCore.Solidity.TypeCheck.CheckedContract :=
  Classical.choose SolidCore.Refinement.Solar.VerifyTokenSource.contract_ok

theorem contract_eq : SolidCore.Verify.VC.Token.contract? = .ok contract :=
  Classical.choose_spec SolidCore.Refinement.Solar.VerifyTokenSource.contract_ok

/-- The source stage's fuel. -/
abbrev fuel : Nat := SolidCore.Verify.VC.Token.fuel

/-- The calls the end-to-end theorem covers. -/
def scope (call : Call) : Prop :=
  stageScope fnTransfer [(2, 4096)] call ∨ stageScope fnBurn [(2, 4096)] call

/-- The call context of SolidCore's and EthLib's interface (\`Refinement.Statement\`): sender
\`0x2000\`, the contract at \`0x1000\`, block timestamp 1. -/
def ctxOf (call : Call) : SolidCore.Spec.Ctx :=
  { sender := 0x2000, value := call.callvalue, timestamp := 1, self := 0x1000 }

/-- The word at argument \`i\` of a call. -/
def argWord (call : Call) (i : Nat) : Int :=
  ((SolidCore.Spec.words ((call.calldata.data.toList.map (·.toNat)).drop 4)).getD i 0 : Nat)

/-- The ghost \`sumBalances\` after a call: \`mint(address,uint256)\` adds its amount and
\`burn(uint256)\` takes its amount away, as the source's ghost updates write it. -/
def step : SolidCore.Spec.GhostStep := fun call g name keys =>
  if name = "sumBalances" ∧ keys = [] then
    if SolidCore.Spec.selectorOf call = 0x40c10f19 then g name keys + argWord call 1
    else if SolidCore.Spec.selectorOf call = 0x42966c68 then g name keys - argWord call 0
    else g name keys
  else g name keys

end Contracts.Token
