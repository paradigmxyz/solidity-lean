import SolidCore.Refinement.Solar.AssembleSim
import c4.gen.Main.Evm5
import c4.gen.Main.Bytecode

/-!
# c4: two packed uint8 fields, from any storage

scripts/refinement/c4/c4.sol (`contract Main { uint8 v; uint8 w = 7; function add(uint8 x) ... }`:
`v += x; w ^= x; return v;`) compiles with solar's default options and -Zcheck-analyses=false to the
final EVM IR `evm5` (after `cfg-simplify-early`) and to 107 bytes of runtime bytecode, both exported
by -Zemit-lean-stages into solar's solar-tv/milestone/c4 and imported from there (c4.gen.Main.Evm5,
c4.gen.Main.Bytecode). solar's
solar-tv/milestone/c4 proves the stages from the first lowered MIR to `evm5`
(`SolarTV.Milestone.C4.c4_mir_to_evmir`); this file proves the last one, `evm5` to the bytecode.

Both fields live in slot 0, `v` in its low byte and `w` in the next: the code reads the slot,
masks `v` out (AND 0xff), adds with the overflow check, merges it back (AND NOT 0xff, OR), reads
`w` with BYTE 30, XORs, shifts it back (SHL 8), merges it (AND NOT 0xff00, OR) and stores the slot.
The layout is three blocks, each jump forward, so the default certificate's potentials suffice.

* `check_ok`: the checker accepts `evm5` and the bytes with `cert`, by the kernel's evaluation.
* `stage`: EVM IR to bytecode is a stage on every call with no value, from any storage, under
  every oracle, from `Assemble.stage_of_check` at `check_ok`.
* `stageAll`: the same on every call, with any value, from `Assemble.stage_of_check_all`.
* `mutantSub_check`, `mutantShl_check`: the checker rejects one-byte mutants, SUB for the
  addition's ADD and SHL for the BYTE that reads `w`.
-/

namespace SolidCore.Refinement.Solar.C4

open SolarTV.Assembly SolarTV.Export.Main

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The calls of the stage: no value, any call data, any storage. -/
def scope (call : SolarTV.Call) : Prop := call.callvalue = 0

/-- The certificate: each block's offset in the code (bb3, the revert, at 0x55; bb7, the
Panic(0x11), at 0x59), the stack height each block needs on entry (none), and the bound on memory
(the return's and the panic's 64 bytes). -/
def cert : Assemble.Cert := { offsets := [0, 0x55, 0x59], needs := [0, 0, 0], top := 64 }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm5 code cert = true := by decide +kernel

/-- EVM IR to bytecode is a stage for c4 on every call with no value, from any storage, under
every oracle: the generic theorem at check_ok. -/
theorem stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm5
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check check_ok o fun _ h => h

/-- EVM IR to bytecode is a stage for c4 on every call, with any value, call data and storage,
under every oracle: `Assemble.stage_of_check_all` at check_ok. -/
theorem stageAll (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm5
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_all check_ok o scope

/-- The bytes with the byte at `i` replaced by `b`. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- The addition's ADD, at offset 0x2b, and the BYTE that reads `w`, at offset 0x3d. -/
theorem mutated_bytes : bytecode[0x2b]? = some 0x01 ∧ bytecode[0x3d]? = some 0x1a := by decide

set_option maxRecDepth 100000 in
/-- SUB for the addition's ADD: the checker rejects it. -/
theorem mutantSub_check : Assemble.check evm5 (mutant 0x2b 0x03) cert = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- SHL for the BYTE that reads `w`: the checker rejects it. -/
theorem mutantShl_check : Assemble.check evm5 (mutant 0x3d 0x1b) cert = false := by decide +kernel

end SolidCore.Refinement.Solar.C4
