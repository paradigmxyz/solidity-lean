import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.AssembleFast
import mulx.gen.Main.Evm8
import mulx.gen.Main.Bytecode

/-!
# mulx: the final EVM IR to solar's bytecode

The test contract scripts/refinement/mulx/mul.sol compiles with solar a8179dfc and
-Zcheck-analyses=false to the final EVM IR evm8 (after terminal-layout) and to 186 bytes of
runtime bytecode (sha256 42ecdc71b09d339299d2b7ce61e121c77b141c5386eb9cbf18792a9ba9ca4cfe),
both exported by -Zemit-lean-stages into solar's solar-tv/milestone/mulx and imported from
there. Solar's milestone proves the stages from the first lowered MIR to evm8
(SolarTV.Milestone.Mulx.mulx_mir_to_evmir); this file proves the last one, evm8 to the
bytecode, with the generic assembler check, whose fragment includes MUL and DIV for this
contract's products and the overflow test of uint256(a) * b * c.

The layout is five blocks: the dispatcher, the empty revert (bb4, at 0x1d), the Panic(0x11)
revert (bb8, at 0x21), n (bb10, at 0x33) and m (bb5, at 0x6d). n and m jump back to the two
reverts, so the certificate gives each block its potential: the reverts' items, a bound on n's
and m's, and the dispatcher's on top of them.

* check_ok: the checker accepts evm8 and the bytes with cert, by the kernel's evaluation of
  its one-pass form (`Assemble.checkFast`, equal to it by `Assemble.check_eq_checkFast`).
* stageAll: EVM IR to bytecode is a stage on every call, with any value, call data and storage,
  under every oracle (Assemble.stage_of_check_all).
* mutantAdd_check, mutantSdiv_check: the checker rejects one-byte mutants, ADD for n's first
  MUL and SDIV for the DIV of its overflow test.
-/

namespace SolidCore.Refinement.Solar.MulX

open SolarTV.Assembly SolarTV.Export.Main

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The certificate: each block's offset in the code, the stack height each block needs on
entry (none), the bound on memory (the return's and the panic's 64 bytes) and each block's
potential, a bound on the items its runs execute. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x1d, 0x21, 0x33, 0x6d], needs := [0, 0, 0, 0, 0], top := 64,
    costs := [200, 4, 10, 100, 100] }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm8 code cert = true := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- EVM IR to bytecode is a stage for mulx on every call, with any value, call data and
storage, under every oracle. -/
theorem stageAll (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm8
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_all check_ok o scope

/-- The bytes with the byte at i replaced by b. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- n's first MUL, at offset 0x53, and the DIV of its overflow test, at offset 0x5c. -/
theorem mutated_bytes : bytecode[0x53]? = some 0x02 ∧ bytecode[0x5c]? = some 0x04 := by decide

set_option maxRecDepth 100000 in
/-- ADD for n's first MUL: the checker rejects it. -/
theorem mutantAdd_check : Assemble.check evm8 (mutant 0x53 0x01) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- SDIV for the DIV of n's overflow test: the checker rejects it. -/
theorem mutantSdiv_check : Assemble.check evm8 (mutant 0x5c 0x05) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.MulX.check_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_ok

/-- info: 'SolidCore.Refinement.Solar.MulX.stageAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stageAll

end SolidCore.Refinement.Solar.MulX
