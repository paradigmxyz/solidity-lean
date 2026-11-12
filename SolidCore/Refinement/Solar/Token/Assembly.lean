import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleFast
import token.gen.Token.Evm11
import token.gen.Token.Bytecode
import token.Proofs.Stages

/-!
# token: the final EVM IR to solar's bytecode

solar-tv/milestone/token/token.sol (an ERC-20 token: balances, nested allowances and a frozen flag
in mappings, a total and an owner; balanceOf, allowance, getOwner, isFrozen, freeze, transfer,
approve and transferFrom, which emit the indexed Transfer and Approval events, revert with
"balance" and "allowance" and skip the allowance's update when it is unlimited) compiles with
solar 3ca8f483 (-Zcheck-analyses=false -Ogas --evm-version osaka) to the final EVM IR evm11 (after
late-word) and to 761 bytes of runtime bytecode (sha256
b6f1c3ab69651bb080d1ac406be62499ca6ba82de76bb1d203a7619404b2c799), both exported by
-Zemit-lean-stages into solar's solar-tv/milestone/token and imported from there. Solar's
milestone proves the stages from the first lowered MIR to evm11
(SolarTV.Milestone.Token.token_mir_to_evmir); this file proves the last one, evm11 to the
bytecode, with the generic assembler check: its mapping slots are KECCAK256 of the key and the
slot at constant offsets, nested for the allowances, it reads CALLER, logs with LOG3, and its two
revert strings share one block that stores the string's offset with PUSH 32; DUP1, a constant the
check follows through the DUP (Assemble.dupKnown). Two jumps go back in the layout (to the shared
tail that logs Transfer, and to the shared revert block), so the certificate gives each block's
potential.

The stage holds under every oracle whose CALLER is the caller of EthLib's calls and whose hash is
EthLib's KECCAK256 (Assemble.OracleOk), so for every calldata, mapping key, caller word the
bytecode sees, value and storage; backend composes it with the MIR to EVM IR stages, which hold
for every oracle.

* check_ok: the checker accepts evm11 and the bytes with cert, by the kernel's evaluation of
  its one-pass form (Assemble.checkFast, equal to it by Assemble.check_eq_checkFast).
* stageOk, stageEth: EVM IR to bytecode is a stage on every call, under every such oracle.
* backend: the first lowered MIR to the bytecode, on every call.
* Mutants.lean: the checker rejects one-byte mutants of the bytecode.
-/

namespace SolidCore.Refinement.Solar.Token

open SolarTV.Assembly SolarTV.Export.Token

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The certificate: each block's offset in the code (every block but the first is a jump
target), the stack height each block needs on entry (the dispatcher's selector for the second
half of the dispatch, the string's words for the shared revert block, the transfer's sender and
recipient for its shared tail), all of it data, the bound on memory (the reverts' 128 bytes), each
block's potential, and that the program reads the caller and hashes. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x3d, 0x41, 0x53, 0x81, 0xa4, 0xdb, 0xeb, 0x114, 0x143, 0x19e, 0x1cc, 0x1da,
      0x1f1, 0x24e, 0x2aa, 0x2e5],
    needs := [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 3, 0], top := 128,
    costs := [155, 4, 10, 143, 27, 41, 12, 31, 34, 85, 11, 19, 14, 47, 132, 62, 21],
    types := [[], [], [], [some false], [], [], [], [], [], [], [some false, some false], [],
      [some false, some false], [], [], [some false, some false, some false], []],
    env := true }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm11 code cert = true := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode is a stage for token on every call, under every oracle whose caller and
hash are EthLib's. -/
theorem stageOk (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm11
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_env check_ok o (fun _ => ho) scope

/-- The same for Assemble.ethOracle o, any oracle with EthLib's caller and hash. -/
theorem stageEth (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem (Assemble.ethOracle o)) SolidCore.Refinement.ethLib evm11
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_eth check_ok o scope

/-- The backend: solar-tv's stages from stage0 to evm11, then the assembly stage, on every call
(any calldata, mapping keys, value and storage), under every oracle with EthLib's caller and
hash. -/
theorem backend (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.mirSem o) SolidCore.Refinement.ethLib stage0
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    (fun call _ => SolarTV.Milestone.Token.token_mir_to_evmir o call trivial) (stageOk o ho scope)

/-- info: 'SolidCore.Refinement.Solar.Token.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.Token.stageOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageOk

/-- info: 'SolidCore.Refinement.Solar.Token.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

end SolidCore.Refinement.Solar.Token

