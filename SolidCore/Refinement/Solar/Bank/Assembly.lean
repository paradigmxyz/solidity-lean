import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleFast
import bank.gen.Bank.Evm11
import bank.gen.Bank.Bytecode
import bank.Proofs.Stages

/-!
# bank: the final EVM IR to solar's bytecode

solar-tv/milestone/bank/bank.sol (a `mapping(address => uint256)` of balances and a total,
credited by an internal function that `deposit(uint256)` calls for `msg.sender`, emitting the indexed
`Deposit` event, and that `depositFor(address,uint256)` calls, and `balanceOf(address)`) compiles with solar
0a455fda to the final EVM IR evm11 (after stack-reschedule) and to 454 bytes of runtime bytecode
(sha256 bff0578068ce4ab4a041f226e4e960c13d358c8b430718fefe9ce3a22d760543), both exported by
-Zemit-lean-stages into solar's solar-tv/milestone/bank and imported from there. Solar's
milestone proves the stages from the first lowered MIR to evm11
(SolarTV.Milestone.Bank.bank_mir_to_evmir); this file proves the last one, evm11 to the
bytecode, with the generic assembler check: its mapping slots are KECCAK256 of the key and the
slot at constant offsets, `deposit` reads CALLER and logs with LOG2, and the internal function is
entered with a pushed return label (blocks 5 and 10, the certificate's `rets`) and returns with a
dynamic JUMP to it, which the certificate's stack types follow.

The stage holds under every oracle whose CALLER is the caller of EthLib's calls and whose hash is
EthLib's KECCAK256 (`Assemble.OracleOk`), so for every calldata, mapping key, caller word the
bytecode sees, value and storage; `backend` composes it with the MIR to EVM IR stages, which hold for
every oracle.

* check_ok: the checker accepts evm11 and the bytes with cert, by the kernel's evaluation of
  its one-pass form (`Assemble.checkFast`, equal to it by `Assemble.check_eq_checkFast`).
* stageOk, stageEth: EVM IR to bytecode is a stage on every call, under every such oracle.
* backend: the first lowered MIR to the bytecode, on every call.
* Mutants.lean: the checker rejects one-byte mutants of the hash, the caller, the log, the
  return label, the return jump and the mapping key.
-/

namespace SolidCore.Refinement.Solar.Bank

open SolarTV.Assembly SolarTV.Export.Bank

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The certificate: each block's offset in the code, the stack height and the types each block
needs on entry (the internal function, block 4, finds its return label on top), the bound on
memory (the reverts' 128 bytes), each block's potential, the blocks a return label names, and
that the program reads the caller and hashes. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x28, 0x2c, 0x3e, 0x4d, 0x87, 0xcb, 0xe1, 0xe5, 0xf8, 0x11b, 0x134, 0x147,
      0x161, 0x193, 0x1a6],
    needs := [0, 0, 6, 1, 5, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3, 8], top := 128,
    costs := [137, 4, 10, 111, 100, 51, 24, 14, 11, 125, 35, 18, 24, 54, 18, 26],
    types := [[], [], [some false, none, none, some false, some false, some false], [some false],
      [some true, some false, some false, some false, some false],
      [some false, some false, some false], [some false], [some false, some false, some false],
      [some false, some false], [some false], [some false, some false, some false],
      [some false, some false], [some false, some false], [some false],
      [some false, some false, some false],
      [some false, some false, some false, some true, some false, some false, some false,
        some false]],
    rets := [5, 10], env := true }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm11 code cert = true := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode is a stage for bank on every call, under every oracle whose caller and
hash are EthLib's. -/
theorem stageOk (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm11
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_env check_ok o (fun _ => ho) scope

/-- The same for `Assemble.ethOracle o`, any oracle with EthLib's caller and hash. -/
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
    (fun call _ => SolarTV.Milestone.Bank.bank_mir_to_evmir o call trivial) (stageOk o ho scope)

/-- info: 'SolidCore.Refinement.Solar.Bank.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.Bank.stageOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageOk

/-- info: 'SolidCore.Refinement.Solar.Bank.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

end SolidCore.Refinement.Solar.Bank
