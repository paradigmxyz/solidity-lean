import SolidCore.Refinement.Solar.AssembleCut

/-!
# Memory at an offset the call chooses: an example and a mutant

A program that loads the word at the memory offset the first word of the call data names, stores
it at offset 0 and returns it. The offset is anything the caller sends, so no bound on it is known
when checking; the checker with GAS accepts the bytecode with a certificate whose memory bound is
`2 ^ 140` bytes, and at every gas below `2 ^ 256` every result of the bytecode is the program's:
a run that succeeds paid for the growth of memory, which keeps it within SolarTV's count of words.
The bytecode with SLOAD in place of MLOAD is rejected by evaluation, and so is the program under a
certificate whose memory bound is too small.
-/

namespace SolidCore.Refinement.Solar.AssembleDynExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Final

/-- PUSH0, CALLDATALOAD, MLOAD, then the word stored at offset 0 and returned. -/
def prog : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0)), .effect .calldataload 1, .op .load, .op (.stack (.push 0)),
      .op .store, .op (.stack (.push 32)), .op (.stack (.push 0)), .ret]] }

/-- PUSH0 CALLDATALOAD MLOAD PUSH0 MSTORE PUSH1 32 PUSH0 RETURN. -/
def code : ByteArray := ⟨#[0x5f, 0x35, 0x51, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

/-- The same code with SLOAD (0x54) in place of MLOAD. -/
def mutant : ByteArray := ⟨#[0x5f, 0x35, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [8], types := [[]] }

def maxs : List Nat := [0]

theorem check_ok : checkC prog code cert maxs = true := by decide +kernel

/-- The mutant fails the check by evaluation. -/
theorem mutant_fails : checkC prog mutant cert maxs = false := by decide +kernel

/-- A memory bound below `2 ^ 140` does not cover loads at offsets the checker does not know. -/
theorem small_top_fails : checkC prog code { cert with top := 2 ^ 32 } maxs = false := by
  decide +kernel

/-- **At every gas below `2 ^ 256`, every result of the bytecode is the program's**, under the
oracle of the run's table. -/
theorem bytecode (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => prog) code scope (RunOracle.CertOk cert) :=
  withinRun_of_checkC check_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleDynExample.bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode

/-- The range the call names, returned: PUSH0 CALLDATALOAD (the size) PUSH1 32 CALLDATALOAD (the
offset) RETURN. -/
def progRet : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0)), .effect .calldataload 1, .op (.stack (.push 32)),
      .effect .calldataload 1, .ret]] }

def codeRet : ByteArray := ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0xf3]⟩

/-- The same code with REVERT (0xfd) in place of RETURN. -/
def mutantRet : ByteArray := ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0xfd]⟩

def certRet : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [5], types := [[]] }

theorem checkRet_ok : checkC progRet codeRet certRet maxs = true := by decide +kernel

theorem mutantRet_fails : checkC progRet mutantRet certRet maxs = false := by decide +kernel

/-- **RETURN of any range the call names**: at every gas below `2 ^ 256`, every result of the
bytecode is the program's. -/
theorem bytecodeRet (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => progRet) codeRet scope (RunOracle.CertOk certRet) :=
  withinRun_of_checkC checkRet_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleDynExample.bytecodeRet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeRet

/-- The hash of the range the call names, returned: PUSH0 CALLDATALOAD (the size) PUSH1 32
CALLDATALOAD (the offset) KECCAK256, then the word stored at offset 0 and returned. -/
def progKec : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0)), .effect .calldataload 1, .op (.stack (.push 32)),
      .effect .calldataload 1, .effect .keccak256 2, .op (.stack (.push 0)), .op .store,
      .op (.stack (.push 32)), .op (.stack (.push 0)), .ret]] }

def codeKec : ByteArray :=
  ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0x20, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

/-- The same code with SWAP1 before KECCAK256, which hashes another range. -/
def mutantKec : ByteArray :=
  ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0x90, 0x20, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def certKec : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [10], types := [[]], env := true }

theorem checkKec_ok : checkC progKec codeKec certKec maxs = true := by decide +kernel

theorem mutantKec_fails : checkC progKec mutantKec certKec maxs = false := by decide +kernel

/-- Without the flag that states EthLib's hash, the checker rejects KECCAK256. -/
theorem unflaggedKec_fails : checkC progKec codeKec { certKec with env := false } maxs = false := by
  decide +kernel

/-- **KECCAK256 of any range the call names**: at every gas below `2 ^ 256`, every result of
the bytecode is the program's under the oracle of the run's table, whose hash is EthLib's. -/
theorem bytecodeKec (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => progKec) codeKec scope (RunOracle.CertOk certKec) :=
  withinRun_of_checkC checkKec_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleDynExample.bytecodeKec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeKec

/-- An event whose data is the range the call names: PUSH0 CALLDATALOAD (the size) PUSH1 32
CALLDATALOAD (the offset) LOG0, then an empty RETURN. -/
def progLog : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0)), .effect .calldataload 1, .op (.stack (.push 32)),
      .effect .calldataload 1, .effect (.log 0) 2, .op (.stack (.push 0)), .op (.stack (.push 0)),
      .ret]] }

def codeLog : ByteArray := ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0xa0, 0x5f, 0x5f, 0xf3]⟩

/-- The same code with LOG1 (0xa1) in place of LOG0. -/
def mutantLog : ByteArray := ⟨#[0x5f, 0x35, 0x60, 0x20, 0x35, 0xa1, 0x5f, 0x5f, 0xf3]⟩

def certLog : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [8], types := [[]] }

theorem checkLog_ok : checkC progLog codeLog certLog maxs = true := by decide +kernel

theorem mutantLog_fails : checkC progLog mutantLog certLog maxs = false := by decide +kernel

/-- **An event with data of any range the call names**: at every gas below `2 ^ 256`, every
result of the bytecode, its logs included, is the program's. -/
theorem bytecodeLog (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => progLog) codeLog scope (RunOracle.CertOk certLog) :=
  withinRun_of_checkC checkLog_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleDynExample.bytecodeLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeLog

/-- The call data echoed: CALLDATASIZE PUSH0 PUSH0 CALLDATACOPY copies all of it to offset 0,
then CALLDATASIZE PUSH0 RETURN returns it. -/
def progCdc : Assemble.Program :=
  { blocks := [[.effect .calldatasize 0, .op (.stack (.push 0)), .op (.stack (.push 0)),
      .effect .calldatacopy 3, .effect .calldatasize 0, .op (.stack (.push 0)), .ret]] }

def codeCdc : ByteArray := ⟨#[0x36, 0x5f, 0x5f, 0x37, 0x36, 0x5f, 0xf3]⟩

/-- The same code with CODECOPY (0x39) in place of CALLDATACOPY. -/
def mutantCdc : ByteArray := ⟨#[0x36, 0x5f, 0x5f, 0x39, 0x36, 0x5f, 0xf3]⟩

def certCdc : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [7], types := [[]] }

theorem checkCdc_ok : checkC progCdc codeCdc certCdc maxs = true := by decide +kernel

theorem mutantCdc_fails : checkC progCdc mutantCdc certCdc maxs = false := by decide +kernel

/-- **A copy of the call data of any size**: at every gas below `2 ^ 256`, every result of the
bytecode is the program's. -/
theorem bytecodeCdc (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => progCdc) codeCdc scope (RunOracle.CertOk certCdc) :=
  withinRun_of_checkC checkCdc_ok scope

/-- info: 'SolidCore.Refinement.Solar.AssembleDynExample.bytecodeCdc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeCdc

end SolidCore.Refinement.Solar.AssembleDynExample
