import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleFast
import events.gen.Events.Evm5
import events.gen.Events.Bytecode
import events.Proofs.Stages

/-!
# events: the final EVM IR to solar's bytecode

solar-tv/milestone/events/events.sol (`transfer(uint256 id, uint256 value)` emitting
`Transfer(address indexed from, uint256 indexed id, uint256 value)` for `msg.sender`) compiles with
solar 0a455fda to the final EVM IR evm5 and to 130 bytes of runtime bytecode (sha256
5ad38c8bca24e0ca8c4a5e95f1f07bf993aad9a02ac3bc0872fc41fab8a6298b), exported by
-Zemit-lean-stages into solar's solar-tv/milestone/events. Solar's milestone proves the stages
from the first lowered MIR to evm5 (SolarTV.Milestone.Events.events_mir_to_evmir); this file
proves evm5 to the bytecode with the generic assembler check: LOG3 with the event's signature,
the caller and the id as topics and the value's word at offset 0 as data, under every oracle whose
CALLER is the caller of EthLib's calls (`Assemble.OracleOk`).

* check_ok: the checker accepts evm5 and the bytes with cert, by the kernel's evaluation of its
  one-pass form (`Assemble.checkFast`, equal to it by `Assemble.check_eq_checkFast`).
* stageOk, backend: EVM IR to bytecode, and the first lowered MIR to bytecode, on every call.
* mutant…_check: the checker rejects one-byte mutants of the caller, the log's topic count, its
  signature topic, its data size and its data offset.
-/

namespace SolidCore.Refinement.Solar.Events

open SolarTV.Assembly SolarTV.Export.Events

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The certificate: the three blocks' offsets (the dispatcher and transfer, the empty revert at
0x53 and the address check's revert at 0x57, which reads one data word from its entry stack),
the reverts' 128 bytes of memory, each block's potential and that the program reads the caller. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x53, 0x57], needs := [0, 0, 1], top := 128, costs := [58, 4, 22],
    types := [[], [], [some false]], env := true }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm5 code cert = true := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode is a stage for events on every call, under every oracle whose caller
and hash are EthLib's. -/
theorem stageOk (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm5
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_env check_ok o (fun _ => ho) scope

/-- The backend: solar-tv's stages from stage0 to evm5, then the assembly stage. -/
theorem backend (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOk o)
    (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.mirSem o) SolidCore.Refinement.ethLib stage0
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    (fun call _ => SolarTV.Milestone.Events.events_mir_to_evmir o call trivial) (stageOk o ho scope)

/-- The bytes with the byte at i replaced by b. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- The bytes the mutants replace: CALLER (0x22), the signature topic's first byte (0x24), the
data size's immediate (0x45), the data offset's PUSH0 (0x46) and LOG3 (0x47). -/
theorem mutated_bytes : bytecode[0x22]? = some 0x33 ∧ bytecode[0x24]? = some 0x7f ∧
    bytecode[0x45]? = some 0x20 ∧ bytecode[0x46]? = some 0x5f ∧ bytecode[0x47]? = some 0xa3 := by
  decide

set_option maxRecDepth 100000 in
/-- ORIGIN for CALLER: rejected. -/
theorem mutantCaller_check : Assemble.check evm5 (mutant 0x22 0x32) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- LOG2 for LOG3: rejected. -/
theorem mutantLog_check : Assemble.check evm5 (mutant 0x47 0xa2) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- Another signature topic: rejected. -/
theorem mutantTopic_check : Assemble.check evm5 (mutant 0x24 0x7e) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- Two words of data for one: rejected. -/
theorem mutantSize_check : Assemble.check evm5 (mutant 0x45 0x40) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The data at MSIZE, another offset: rejected. -/
theorem mutantOffset_check : Assemble.check evm5 (mutant 0x46 0x59) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode from any caller: on every call from the account `a`, any account but the
contract's, under every oracle whose caller is `a` and whose hash is EthLib's. -/
theorem stageOkFrom (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOkAt a o) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) (SolidCore.Refinement.ethLibFrom a) evm5
      (show (SolidCore.Refinement.ethLibFrom a).Prog from code) scope :=
  Assemble.stage_of_check_envFrom a hAB check_ok o (fun _ => ho) scope

/-- The backend from any caller: solar-tv's stages from stage0 to evm5, then the assembly stage,
on every call from the account `a`, under every oracle whose caller is `a` and whose hash is
EthLib's. -/
theorem backendFrom (a : Nat) (hAB : Target.address selfAddress ≠ Target.address a)
    (o : SolarTV.Machine.Oracle) (ho : Assemble.OracleOkAt a o) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.mirSem o) (SolidCore.Refinement.ethLibFrom a) stage0
      (show (SolidCore.Refinement.ethLibFrom a).Prog from code) scope :=
  SolarTV.Stage.trans (B := SolarTV.evmirSem o)
    (fun call _ => SolarTV.Milestone.Events.events_mir_to_evmir o call trivial) (stageOkFrom a hAB o ho scope)

/-- info: 'SolidCore.Refinement.Solar.Events.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.Events.backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backend

/-- info: 'SolidCore.Refinement.Solar.Events.backendFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms backendFrom

end SolidCore.Refinement.Solar.Events
