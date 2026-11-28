import SolidCore.Refinement.Solar.AssembleSim
import SolidCore.Refinement.Solar.RequireModulo.Evm10
import SolidCore.Refinement.Solar.RequireModulo.Bytecode

/-!
# RequireModuloCases: a turned branch, fallthroughs and a backward jump

solar's UI test tests/ui/codegen/lowering/evm-ir/constructs/require_modulo_chain.sol compiles
`RequireModuloCases` (`chain(a, b)`: `require(a % b == 0)`, `require(b % 3 == 0 || a % 2 == 0)`,
`return a + b`) with -Ogas --evm-version osaka to the final EVM IR `evm10` (after `block-layout`,
Evm10.lean) and to 103 bytes of runtime bytecode (Bytecode.lean), both exported by
-Zemit-lean-stages and committed verbatim.

Its layout needs what the generic assembly theorem used to reject: block 0 ends in
`jumpi 1; jump 2` with block 1 next, which the assembler turns into `ISZERO; PUSH bb2; JUMPI`
falling into block 1; blocks 1 and 4 end in a jump to the next block, which the code falls into;
and block 6 jumps back to block 5 (the shared panic tail), which the default potentials, the items
to the end of the layout, cannot bound.

* `check_ok`: the checker accepts `evm10` and the bytes with `cert`, by the kernel's evaluation.
* `stage`: EVM IR to bytecode is a stage on every call with no value, from any storage, under
  every oracle, from `Assemble.stage_of_check` at `check_ok`.
* `stageAll`: the same on every call, with any value, from `Assemble.stage_of_check_all`.
* `unturned_check`, `forward_check`: without the turned block or without the potentials the
  checker rejects the same bytes, so the stage needs both.
* `mutantNot_check`, `mutantDiv_check`: the checker rejects one-byte mutants, NOT for the turned
  branch's ISZERO and DIV for the first MOD.
-/

namespace SolidCore.Refinement.Solar.RequireModulo

open SolarTV.Assembly SolarTV.Export.RequireModuloCases

/-- The runtime bytecode solar exported. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The calls of the stage: no value, any call data, any storage. -/
def scope (call : SolarTV.Call) : Prop := call.callvalue = 0

/-- The certificate: each block's offset, the stack height each block needs on entry, the bound
on memory (the panic's 64 bytes), block 0's branch turned, and each block's potential, the most
items a run from it executes. -/
def cert : Assemble.Cert :=
  { offsets := [0, 0x33, 0x3a, 0x4a, 0x4e, 0x51, 0x61], needs := [0, 3, 3, 0, 2, 3, 2], top := 64,
    turned := [0], costs := [62, 26, 21, 3, 10, 8, 12] }

set_option maxRecDepth 100000 in
/-- The checker accepts solar's bytecode for the program, by the kernel's evaluation. -/
theorem check_ok : Assemble.check evm10 code cert = true := by decide +kernel

/-- EVM IR to bytecode is a stage for RequireModuloCases on every call with no value, from any
storage, under every oracle: the generic theorem at check_ok. -/
theorem stage (o : SolarTV.Machine.Oracle) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm10
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check check_ok o fun _ h => h

/-- EVM IR to bytecode is a stage for RequireModuloCases on every call, with any value, call data and storage,
under every oracle: `Assemble.stage_of_check_all` at check_ok. -/
theorem stageAll (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.evmirSem o) SolidCore.Refinement.ethLib evm10
      (show SolidCore.Refinement.ethLib.Prog from code) scope :=
  Assemble.stage_of_check_all check_ok o scope

set_option maxRecDepth 100000 in
/-- Without block 0 turned, the lowering expects `PUSH bb1; JUMPI` where the code has
`ISZERO; PUSH bb2; JUMPI`: the walk fails, and so does the checker. -/
theorem unturned_check : Assemble.check evm10 code { cert with turned := [] } = false ∧
    walk (Assemble.bytesOf code) cert.offset 0 (Assemble.lower evm10 { cert with turned := [] })
      = none := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- With the default potentials the walk still matches, but block 6's jump back to block 5 finds
the items from block 5 to the end of the layout more than those left in block 6, and the block
check fails. -/
theorem forward_check : Assemble.check evm10 code { cert with costs := [] } = false ∧
    (walk (Assemble.bytesOf code) cert.offset 0 (Assemble.lower evm10 cert)).isSome ∧
    Assemble.blocksOk evm10 { cert with costs := [] } 0 evm10.blocks = false := by
  decide +kernel

/-- The bytes with the byte at `i` replaced by `b`. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- The turned branch's ISZERO, at offset 47, and the first MOD, at offset 39. -/
theorem mutated_bytes : bytecode[47]? = some 0x15 ∧ bytecode[39]? = some 0x06 := by decide

set_option maxRecDepth 100000 in
/-- NOT for the turned branch's ISZERO: the checker rejects it. -/
theorem mutantNot_check : Assemble.check evm10 (mutant 47 0x19) cert = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- DIV for the first MOD: the checker rejects it. -/
theorem mutantDiv_check : Assemble.check evm10 (mutant 39 0x04) cert = false := by decide +kernel

end SolidCore.Refinement.Solar.RequireModulo
