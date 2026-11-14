import SolidCore.Refinement.Solar.AssembleLoopWithin

/-!
# The checker of code with loops on environment reads: an example and a mutant

A program that reads the block's timestamp and the contract's address, compares them as signed
integers (SLT) and returns the result: the checker accepts its bytecode, so at every gas every
result of the bytecode is the program's under every oracle whose reads of the block and the
transaction are EthLib's (`Assemble.EnvOk`), which `Assemble.envOracle` gives every oracle. The
bytecode with NUMBER in place of TIMESTAMP is rejected: the checker's decoding of the code
differs from the program's lowering, by evaluation, not by a timeout.
-/

namespace SolidCore.Refinement.Solar.AssembleLoopEnv

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop SolidCore.Refinement.Final

/-- TIMESTAMP, ADDRESS, SLT, then the word at offset 0 returned. -/
def prog : Assemble.Program :=
  { blocks := [[.effect (.env "timestamp") 0, .effect .address 0, .op (.stack .slt),
      .op (.stack (.push 0)), .op .store, .op (.stack (.push 32)), .op (.stack (.push 0)), .ret]] }

/-- TIMESTAMP ADDRESS SLT PUSH0 MSTORE PUSH1 32 PUSH0 RETURN. -/
def code : ByteArray := ⟨#[0x42, 0x30, 0x12, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

/-- The same code with NUMBER (0x43) in place of TIMESTAMP. -/
def mutant : ByteArray := ⟨#[0x43, 0x30, 0x12, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 32, costs := [8], types := [[]], reads := true }

def maxs : List Nat := [0]

theorem check_ok : checkL prog code cert maxs = true := by decide +kernel

/-- The mutant fails the check by evaluation. -/
theorem mutant_fails : checkL prog mutant cert maxs = false := by decide +kernel

/-- Without the flag that states the environment hypothesis, the checker rejects the reads. -/
theorem unflagged_fails : checkL prog code { cert with reads := false } maxs = false := by
  decide +kernel

/-- **At every gas, every result of the bytecode is the program's**, under every oracle whose
reads of the block and the transaction are EthLib's. -/
theorem bytecode (o : SolarTV.Machine.Oracle) (he : Assemble.EnvOk o) (scope : SolarTV.Call → Prop)
    (gas : Nat) : Within (SolarTV.evmirSem o) (ethLibWith gas) prog code scope :=
  within_of_checkL check_ok o (fun h => absurd h (by decide)) scope gas (fun _ => he)

/-- The hypothesis is met: every oracle's form with EthLib's environment satisfies it. -/
theorem bytecode_env (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) (gas : Nat) :
    Within (SolarTV.evmirSem (Assemble.envOracle o)) (ethLibWith gas) prog code scope :=
  bytecode _ (Assemble.envOracle_ok o) scope gas

/-- info: 'SolidCore.Refinement.Solar.AssembleLoopEnv.bytecode_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode_env

end SolidCore.Refinement.Solar.AssembleLoopEnv
