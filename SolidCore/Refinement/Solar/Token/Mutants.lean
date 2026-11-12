import SolidCore.Refinement.Solar.Token.Assembly

/-!
# token: one-byte mutants of the bytecode

The assembler check rejects the bytecode with one byte changed where the token's behaviour
turns on it: the transfer's balance test, the caller it debits, the Transfer event's log and
signature, a mapping slot's hash, the allowances' slot, the shared revert block's string offset
(a constant the check follows through a DUP), the unlimited allowance's test and the frozen
check's jump. Each rejection is the kernel's evaluation of the check's one-pass form
(Assemble.checkFast).
-/

namespace SolidCore.Refinement.Solar.Token

open SolarTV.Assembly SolarTV.Export.Token

/-- The bytes with the byte at i replaced by b. -/
def mutant (i b : Nat) : ByteArray := ⟨((bytecode.set i b).map UInt8.ofNat).toArray⟩

/-- The bytes the mutants replace: transfer's LT of the balance and the value (0x177), its CALLER
for the frozen flag's key (0x152), its LOG3 (0x1c3), the first byte of the Transfer signature
(0x1a0), balanceOf's KECCAK256 (0x9c), allowance's slot 1 (0xc0), the revert block's DUP1 of the
string offset 32 (0x1dd), transferFrom's ISZERO of the allowance's NOT (0x28a) and the frozen
check's JUMPI (0x164). -/
theorem mutated_bytes : bytecode[0x177]? = some 0x10 ∧ bytecode[0x152]? = some 0x33 ∧
    bytecode[0x1c3]? = some 0xa3 ∧ bytecode[0x1a0]? = some 0xdd ∧ bytecode[0x9c]? = some 0x20 ∧
    bytecode[0xc0]? = some 0x01 ∧ bytecode[0x1dd]? = some 0x80 ∧ bytecode[0x28a]? = some 0x15 ∧
    bytecode[0x164]? = some 0x57 := by decide

set_option maxRecDepth 100000 in
/-- GT for the balance test's LT: rejected. -/
theorem mutantLt_check : Assemble.check evm11 (mutant 0x177 0x11) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- ORIGIN for CALLER: rejected. -/
theorem mutantCaller_check : Assemble.check evm11 (mutant 0x152 0x32) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- LOG2 for the Transfer event's LOG3: rejected. -/
theorem mutantLog_check : Assemble.check evm11 (mutant 0x1c3 0xa2) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- Another signature topic: rejected. -/
theorem mutantTopic_check : Assemble.check evm11 (mutant 0x1a0 0xde) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- ADD for the hash of the mapping slot: rejected. -/
theorem mutantKeccak_check : Assemble.check evm11 (mutant 0x9c 0x01) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The frozen flags' slot 2 for the allowances' slot 1: rejected. -/
theorem mutantSlot_check : Assemble.check evm11 (mutant 0xc0 0x02) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- DUP2 for the DUP1 of the revert string's offset, an MSTORE at an offset the check does not
know: rejected. -/
theorem mutantDup_check : Assemble.check evm11 (mutant 0x1dd 0x81) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- POP for the ISZERO of the unlimited allowance's test: rejected. -/
theorem mutantAllOnes_check : Assemble.check evm11 (mutant 0x28a 0x50) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

set_option maxRecDepth 100000 in
/-- JUMP for the frozen check's JUMPI: rejected. -/
theorem mutantFrozen_check : Assemble.check evm11 (mutant 0x164 0x56) cert = false := by
  rw [Assemble.check_eq_checkFast]
  decide +kernel

/-- info: 'SolidCore.Refinement.Solar.Token.mutantDup_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mutantDup_check

end SolidCore.Refinement.Solar.Token

