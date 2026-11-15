import SolidCore.Refinement.Solar.AssembleRevertCut

/-!
# A revert of the call data, of any size: an example and mutants

The program copies all of its call data to memory at offset 0 (CALLDATACOPY, a copy of a size the
call chooses, which only the checker with GAS and memory at any offset admits) and reverts with
it. `withinRunR_of_checkC` gives, at every gas below `2 ^ 256` and for every call, an oracle under
which every result of the bytecode is the program's, its revert with the call data as revert data
among them, unless the run halted exceptionally.

The mutant that copies from offset 1 reverts with other data, and the one that returns instead
reverts nothing: the checker rejects both by evaluation.
-/

namespace SolidCore.Refinement.Solar.AssembleRevertCutExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleRevertCut

/-- CALLDATASIZE PUSH0 PUSH0 CALLDATACOPY, then CALLDATASIZE PUSH0 REVERT. -/
def prog : Assemble.Program :=
  { blocks := [[.effect .calldatasize 0, .op (.stack (.push 0)), .op (.stack (.push 0)),
      .effect .calldatacopy 3, .effect .calldatasize 0, .op (.stack (.push 0)), .revert]] }

def code : ByteArray := ⟨#[0x36, 0x5f, 0x5f, 0x37, 0x36, 0x5f, 0xfd]⟩

/-- The copy from offset 1 of the call data: PUSH1 1 in place of the first PUSH0. -/
def mutantData : ByteArray := ⟨#[0x36, 0x60, 0x01, 0x5f, 0x37, 0x36, 0x5f, 0xfd]⟩

/-- RETURN (0xf3) in place of REVERT. -/
def mutantReturn : ByteArray := ⟨#[0x36, 0x5f, 0x5f, 0x37, 0x36, 0x5f, 0xf3]⟩

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [7], types := [[]] }

def maxs : List Nat := [0]

theorem check_ok : checkC prog code cert maxs = true := by decide +kernel

/-- The mutant that reverts with other data fails the check by evaluation. -/
theorem mutantData_fails : checkC prog mutantData cert maxs = false := by decide +kernel

/-- The mutant that returns fails the check by evaluation. -/
theorem mutantReturn_fails : checkC prog mutantReturn cert maxs = false := by decide +kernel

/-- **At every gas below `2 ^ 256`, every result of the bytecode is the program's**: its revert
with the call data, unless the run halted exceptionally, under an oracle of each run that meets
the certificate's constraints. -/
theorem bytecode : ∀ gas, gas < 2 ^ 256 → ∀ call, ∃ o, RunOracle.CertOk cert o ∧
    WithinR (SolarTV.evmirSem o) gas prog code (· = call) :=
  withinRunR_of_checkC check_ok

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertCutExample.bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode

end SolidCore.Refinement.Solar.AssembleRevertCutExample
