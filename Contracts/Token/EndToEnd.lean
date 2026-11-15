import Contracts.Token.Lowering
import Contracts.Token.Assembly
import Contracts.Token.Discharge
import SolidCore.Refinement.Keccak.TwoWords
import SolidCore.Refinement.Solar.Hex
import verify_token.gen.Token.Manifest

/-!
# solar-verify's Token: its spec holds of solar's bytecode

solar-verify's Token (scripts/verify/Token.sol, compiled by solar as
Certified/verify_token/verify_token.sol, the same bytes) from its checked obligations to the 685
bytes of runtime bytecode solar emits for it, every step a theorem:

1. the source stage (Lowering.lean): SolidCore's checked Token to solar's first lowered MIR
   stage0, by the generic check, for `transfer`, `burn`, `mint`, `totalSupply` and `owner`;
2. solar-tv's backend stages from stage0 to the final EVM IR evm12 (Certified/verify_token) and the
   assembly stage from evm12 to the bytecode (Assembly.lean);
3. solar-verify's triples of SolidCore's Token (Contracts/Token/VC): `burn_triple`, with no
   hypothesis, and `transfer_triple_discharged` (Discharge.lean: the obligations the kernel checks
   solar-verify's script has, proved in Lean), whose one hypothesis is injectivity of the mapping
   slot on address keys.

The stages hold under every oracle with EthLib's caller and Keccak-256 (`oracle` is one, and the
source stage's hash of two words is EthLib's by `Keccak.ethKeccak_twoWords`), so the composition
is about EthLib's run of the bytes alone (`Target.run`).

* `burn_spec_bytecode`: on every call of `burn(uint256)` in solar-verify's binding scope (any argument
  word, no value, any storage that writes `owner`'s slot), EthLib runs the bytecode to an observable
  that meets `burnPost` (on success the caller's balance and the total supply drop by the
  amount). No hypothesis.
* `spec_holds_of_bytecode`: the same for `transfer(address,uint256)`'s three ensures clauses on
  distinct addresses (`trPost`) and for `burn`, given `HashInj` alone (an explicit
  hypothesis, never an axiom; no solver verdict).
* `certified`: the stage from SolidCore's checked Token to the bytecode for each checked function,
  `mint` included; `manifest_hex`: the bytes are the exporter's manifest hex.

Negatives: the source check rejects a `transfer` that drops the recipient's credit and a `burn` that
writes the supply to `owner`'s slot (`VerifyTokenSource.check_rejects_*`), the assembly check rejects a
retargeted dispatch jump (`VerifyTokenAsm.mutant_check`), and solar-verify's checked script rejects
source and spec mutants (Contracts/Token/VC/Mutants.lean). Not covered: deployment (the constructor),
gas limits other than EthLib's default, calls with value, and the getter `balanceOf` (a public
mapping getter, outside the generic source stage's fragment).
-/

namespace Contracts.Token

open SolidCore.Refinement SolidCore.Refinement.Solar SolidCore.Verify SolidCore.Verify.VC
open SolidCore.Verify.VC.Token
open SolidCore.Refinement.Solar.VerifyTokenSource (stage checkOn check_transfer_eq check_burn_eq
  check_mint_eq contract_ok)
open SolidCore.Refinement.Solar.VerifyTokenAsm (code backend)
open SolarTV.Export.Token (stage0)

/-- The oracle with EthLib's caller and Keccak-256, every other field constant. -/
def oracle : SolarTV.Machine.Oracle :=
  { env := fun _ _ _ => 0, result := fun _ => 0, storageAfter := fun _ _ => 0,
    transientAfter := fun _ _ => 0,
    keccak := fun bytes => EthLib.Execution.Evm.keccak ⟨(bytes.map UInt8.ofBitVec).toArray⟩,
    caller := BitVec.ofNat 160 SolidCore.Refinement.callerAddress }

/-- Its caller is SolidCore's and its hash of two words SolidCore's slot hash. -/
theorem oracle_sourceEnvOk : Generic.SourceEnvOk oracle :=
  ⟨by unfold Generic.CallerOk; decide +kernel,
    fun a b _ _ => SolidCore.Refinement.Keccak.ethKeccak_twoWords a b⟩

/-- Its caller and hash are EthLib's. -/
theorem oracle_ok : Assemble.OracleOk oracle :=
  ⟨show (BitVec.ofNat 160 callerAddress).setWidth 256 = (Target.address callerAddress).toU256 by
    decide +kernel, fun _ => rfl⟩

/-- **SolidCore's checked Token to solar's bytecode**, for each function the source check accepts,
on solar-verify's binding scope. -/
theorem certified {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    {fn : SolidCore.Refinement.Abi.Fn} (h : checkOn stage0 fn = some true) :
    SolarTV.Stage (solidCore fuel) ethLib c code (stageScope fn [(2, 4096)]) :=
  SolarTV.Stage.trans (stage oracle oracle_sourceEnvOk hc h) (backend oracle oracle_ok _)

/-- A total-correctness triple of SolidCore's Token on a checked function holds of the bytecode. -/
theorem bytecode_of_triple {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) {fn : SolidCore.Refinement.Abi.Fn} (h : checkOn stage0 fn = some true)
    {post : Call → Observable → Prop}
    (ht : Triple fuel c (stageScope fn [(2, 4096)]) (fun _ => True) post) :
    ∀ call, stageScope fn [(2, 4096)] call →
      ∃ obs, Target.run code call = some obs ∧ post call obs := by
  intro call hs
  obtain ⟨hsome, hpost⟩ := ht call hs trivial
  obtain ⟨obs, hobs⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨obs, certified hc h call hs obs hobs, hpost obs hobs⟩

/-- **Token's `burn` on solar's bytecode**, with no hypothesis: every call of `burn(uint256)` in
solar-verify's binding scope runs, under EthLib, to an observable meeting `burnPost`. -/
theorem burn_spec_bytecode :
    ∀ call, stageScope fnBurn [(2, 4096)] call →
      ∃ obs, Target.run code call = some obs ∧ burnPost call obs := by
  obtain ⟨c, hc⟩ := contract_ok
  exact bytecode_of_triple hc (fn := fnBurn) check_burn_eq (burn_triple hc)

/-- **solar-verify's spec of Token holds of solar's bytecode**: given injectivity of the mapping slot
on address keys (Keccak-256 of an address and slot 0), every call of
`transfer(address,uint256)` in the binding scope runs under EthLib to an observable meeting
`transfer`'s ensures clauses on distinct addresses, and every call of `burn` to one meeting
`burn`'s. -/
theorem spec_holds_of_bytecode (inj : HashInj) :
    (∀ call, stageScope fnTransfer [(2, 4096)] call →
      ∃ obs, Target.run code call = some obs ∧ trPost call obs) ∧
    (∀ call, stageScope fnBurn [(2, 4096)] call →
      ∃ obs, Target.run code call = some obs ∧ burnPost call obs) := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨bytecode_of_triple hc (fn := fnTransfer) check_transfer_eq (transfer_triple_discharged inj hc),
    burn_spec_bytecode⟩

open SolarTV.Export.Token Hex in
set_option maxRecDepth 100000 in
/-- The manifest's hex is the lowercase hex of the bytes the stages run. -/
theorem manifest_hex : Manifest.bytecodeHex = String.ofList (hexChars bytecode) := by rfl

/-- info: 'Contracts.Token.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified

/-- info: 'Contracts.Token.burn_spec_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms burn_spec_bytecode

/-- info: 'Contracts.Token.spec_holds_of_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spec_holds_of_bytecode

end Contracts.Token

