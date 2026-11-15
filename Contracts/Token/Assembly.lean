import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleFast
import verify_token.gen.Token.Evm12
import verify_token.gen.Token.Bytecode
import verify_token.Proofs.Stages

/-!
# solar-verify's Token: the final EVM IR to solar's bytecode

solar compiles solar-verify's Token (Certified/verify_token/verify_token.sol, byte for byte
scripts/verify/Token.sol) to the final EVM IR evm12 (after `late-word`) and to 685 bytes of runtime
bytecode, both exported by -Zemit-lean-stages into Certified/verify_token/gen. Certified/verify_token
proves solar-tv's backend stages from the first lowered MIR stage0 to evm12
(`SolarTV.Milestone.VerifyToken.verify_token_mir_to_evmir`); this file proves the last one, evm12
to the bytecode, with the generic assembler check: the balances mapping's slots are KECCAK256 of the
key and slot 0 at constant offsets, `transfer`, `mint` and `burn` read CALLER, every jump goes to a
labelled block, and the checked arithmetic's panics and the reverts write memory below 128 bytes.

* `check_ok`: the checker accepts evm12 and the bytes with `cert`, by the kernel's evaluation of its
  one-pass form (`Assemble.checkFast`).
* `stageOk`: EVM IR to bytecode is a stage on every call, under every oracle whose caller and hash
  are EthLib's (`Assemble.OracleOk`).
* `backend`: stage0 to the bytecode, on every call, under every such oracle.
* `mutant_check`: the checker rejects the bytecode with `transfer`'s dispatch jump retargeted.

The certificate's numbers are not trusted: offsets are where the walk finds each block's
JUMPDEST, needs and types the lowest stack each block is entered with (all data), costs each
block's potential, and the checker re-derives every claim from them.
-/

namespace SolidCore.Refinement.Solar.VerifyTokenAsm

open SolidCore.Refinement.Solar SolarTV.Export.Token

/-- The runtime bytecode solar exported with the stages. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The certificate: each block's offset in the code, the lowest stack height each block is
entered with (every entry word is data), the bound on memory (128 bytes), each block's potential
(the items any run from its entry executes, at most), and that the program reads the caller and
hashes. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x47, 0x4b, 0x5d, 0x8f, 0x99, 0xa9, 0x10c, 0x11c, 0x12c, 0x134, 0x145, 0x149,
      0x159, 0x172, 0x1dd, 0x1ee, 0x1f8, 0x20f, 0x22a, 0x243, 0x27f, 0x293],
    needs := [0, 0, 3, 1, 1, 1, 1, 3, 5, 2, 4, 4, 3, 4, 1, 2, 4, 7, 7, 7, 1, 3, 5],
    top := 128,
    costs := [142, 3, 9, 56, 7, 11, 85, 19, 14, 5, 19, 16, 13, 27, 105, 23, 20, 21, 31, 31, 61,
      20, 28],
    types := [0, 0, 3, 1, 1, 1, 1, 3, 5, 2, 4, 4, 3, 4, 1, 2, 4, 7, 7, 7, 1, 3, 5].map
      (fun n => List.replicate n (some false)),
    env := true }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for evm12, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm12 code cert = true := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode is a stage on every call, under every oracle whose caller and hash are
EthLib's. -/
theorem stageOk (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm12
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_env check_ok o (fun _ => ho) scope

/-- The backend: solar-tv's stages from stage0 to evm12, then the assembly stage, on every call
(any calldata, mapping keys, value and storage), under every oracle with EthLib's caller and
hash. -/
theorem backend (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.mirSem o) SolidCore.Refinement.ethLib stage0
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    (fun call _ => SolarTV.Milestone.VerifyToken.verify_token_mir_to_evmir o call trivial)
    (stageOk o ho scope)

/-- The bytecode with `transfer`'s dispatch (`PUSH2 0x0172` at byte 0x43) sent to block 13's
JUMPDEST (0x0159) instead. -/
def mutant : ByteArray := ⟨((bytecode.set 0x45 0x59).map UInt8.ofNat).toArray⟩

set_option maxRecDepth 100000 in
/-- The checker rejects the retargeted jump: the walk finds a push of 0x0159 where the layout
puts block 14 at 0x0172. -/
theorem mutant_check : Assemble.check evm12 mutant cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.VerifyTokenAsm.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.VerifyTokenAsm.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

end SolidCore.Refinement.Solar.VerifyTokenAsm

