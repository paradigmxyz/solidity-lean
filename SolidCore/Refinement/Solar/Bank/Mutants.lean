import SolidCore.Refinement.Solar.Bank.Assembly

/-!
# bank: one-byte mutants of the bytecode

The assembler check rejects the bytecode with one byte changed where the assembly stage's
fragment for bank is new: the mapping slot's hash, the caller, the event's log, the return
label the internal call pushes, the internal function's return jump and the key it hashes. Each
rejection is the kernel's evaluation of the check's one-pass form (`Assemble.checkFast`).
-/

namespace SolidCore.Refinement.Solar.Bank

open SolarTV.Assembly SolarTV.Export.Bank

/-- The bytes with the byte at i replaced by b. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- The bytes the mutants replace: the mapping slot's KECCAK256 (0x58), `deposit`'s CALLER (0x4a),
its LOG2 (0xb0), the return label it pushes (0x4c, the immediate 0x87), the internal function's
return JUMP (0x86) and the DUP2 of the key it stores for the hash (0x4e). -/
theorem mutated_bytes : bytecode[0x58]? = some 0x20 ∧ bytecode[0x4a]? = some 0x33 ∧
    bytecode[0xb0]? = some 0xa2 ∧ bytecode[0x4c]? = some 0x87 ∧ bytecode[0x86]? = some 0x56 ∧
    bytecode[0x4e]? = some 0x81 := by decide

set_option maxRecDepth 100000 in
/-- ADD for the hash of the mapping slot: rejected. -/
theorem mutantKeccak_check : Assemble.check evm11 (mutant 0x58 0x01) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- ORIGIN for CALLER: rejected. -/
theorem mutantCaller_check : Assemble.check evm11 (mutant 0x4a 0x32) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- LOG1 for the event's LOG2: rejected. -/
theorem mutantLog_check : Assemble.check evm11 (mutant 0xb0 0xa1) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- A return label one byte past its block: rejected. -/
theorem mutantLabel_check : Assemble.check evm11 (mutant 0x4c 0x88) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- STOP for the return jump: rejected. -/
theorem mutantReturn_check : Assemble.check evm11 (mutant 0x86 0x00) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- DUP3 for the key's DUP2, so the hash reads another word as the key: rejected. -/
theorem mutantKey_check : Assemble.check evm11 (mutant 0x4e 0x82) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

end SolidCore.Refinement.Solar.Bank
