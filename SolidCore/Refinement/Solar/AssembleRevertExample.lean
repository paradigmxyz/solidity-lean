import SolidCore.Refinement.Solar.AssembleRevert

/-!
# A program that reverts with data the call chooses: an example and a mutant

The program loads the first word of its calldata, stores it at offset 0 and reverts with that
word: `withinR_of_checkL` gives, at every gas, under every oracle, that every result of its bytecode
is the program's, a revert among them (with the calldata's first word as its revert data), unless
the run halted exceptionally (out of gas). `Final.Within` would let a reverting bytecode stand
for itself; `WithinR` does not.

The mutant loads the calldata word at offset 4 instead, so it reverts with other data: the checker
rejects it by evaluation, not by a timeout.
-/

namespace SolidCore.Refinement.Solar.AssembleRevertExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Final

/-- PUSH 0, CALLDATALOAD, PUSH 0, MSTORE, PUSH 32, PUSH 0, REVERT. -/
def prog : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0)), .effect .calldataload 1, .op (.stack (.push 0)), .op .store,
      .op (.stack (.push 32)), .op (.stack (.push 0)), .revert]] }

/-- PUSH0 CALLDATALOAD PUSH0 MSTORE PUSH1 32 PUSH0 REVERT. -/
def code : ByteArray := ⟨#[0x5f, 0x35, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xfd]⟩

/-- The same code loading the calldata word at offset 4: PUSH1 4 in place of the first PUSH0. -/
def mutant : ByteArray := ⟨#[0x60, 0x04, 0x35, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xfd]⟩

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 32, costs := [7], types := [[]] }

def maxs : List Nat := [0]

theorem check_ok : checkL prog code cert maxs = true := by decide +kernel

/-- The mutant, which reverts with other data, fails the check by evaluation. -/
theorem mutant_fails : checkL prog mutant cert maxs = false := by decide +kernel

/-- **At every gas, every result of the bytecode is the program's**: its revert with the
calldata's first word, unless the run halted exceptionally, under every oracle. -/
theorem bytecode (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) (gas : Nat) :
    WithinR (SolarTV.evmirSem o) gas prog code scope :=
  withinR_of_checkL check_ok o (fun h => absurd h (by decide)) scope gas

/-- The same below `2 ^ 256` gas, in the form of `Final.Within` too. -/
theorem bytecode_within (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) (gas : Nat)
    (_ : gas < 2 ^ 256) : Within (SolarTV.evmirSem o) (ethLibWith gas) prog code scope :=
  (bytecode o scope gas).within

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertExample.bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode

/-- info: 'SolidCore.Refinement.Solar.AssembleRevertExample.mutant_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutant_fails

end SolidCore.Refinement.Solar.AssembleRevertExample
