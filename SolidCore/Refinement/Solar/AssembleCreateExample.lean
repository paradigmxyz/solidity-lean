import SolidCore.Refinement.Solar.AssembleCut

/-!
# CALL with value, CODECOPY and CREATE2: the checker on an example and its mutants

A program in one block that copies 8 bytes of its own code from offset 2 to memory at 0x80
(CODECOPY, its destination a DUP of the free memory word over the known code offset), creates a
contract from them with CREATE2 and salt 0x2a, calls the new address with value 1 (CALL), and
returns the call's flag. The checker of code with calls and creations (`AssembleCut.checkCF`)
accepts its bytecode under a certificate that says the program makes calls and creates.

Rejected by evaluation: the bytecode with salt 0x2b, the bytecode sending value 2, the bytecode
copying from code offset 3, the certificates that say the program does not create or makes no call,
the gated checker `AssembleCut.checkCB`, a program whose code offset is a call data word (not known
to the checker), and a program whose known code offset is 2 ^ 32.

Scope: this is the checker only. The theorem over runs of programs `checkCF` accepts (the segment
proof with the run's tables of calls and creations, `createOracle (tableOracle base T) A`) is not
proved yet, so nothing here says the bytecode refines the program.
-/

namespace SolidCore.Refinement.Solar.AssembleCreateExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut

/-- The program, from its code offset, salt and call value. -/
def progOf (off salt value : Assemble.Word) : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0x80)), .op (.stack (.push 8)), .op (.stack (.push off)),
      .op (.stack (.dup 2)), .effect .codecopy 3,
      .op (.stack (.push salt)), .op (.stack (.push 8)), .op (.stack (.dup 2)),
      .op (.stack (.push 0)), .effect .create2 4,
      .op (.stack (.push 0)), .op (.stack (.push 0)), .op (.stack (.push 0)), .op (.stack (.push 0)),
      .op (.stack (.push value)), .op (.stack (.dup 5)), .effect .gas 0, .effect (.call .call) 7,
      .op (.stack (.push 0)), .op .store, .op (.stack (.push 32)), .op (.stack (.push 0)), .ret]] }

def prog : Assemble.Program := progOf 2 0x2a 1

/-- The bytecode, from the bytes of its code offset, salt and call value. -/
def codeOf (off salt value : UInt8) : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x08, 0x60, off, 0x82, 0x39,
    0x60, salt, 0x60, 0x08, 0x82, 0x5f, 0xf5,
    0x5f, 0x5f, 0x5f, 0x5f, 0x60, value, 0x85, 0x5a, 0xf1,
    0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def code : ByteArray := codeOf 2 0x2a 1

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [23], types := [[]], calls := true,
    creates := true }

def maxs : List Nat := [0]

theorem check_ok : checkCF prog code cert maxs = true := by decide +kernel

/-- The salt mutant: CREATE2 with salt 0x2b. -/
theorem mutantSalt_fails : checkCF prog (codeOf 2 0x2b 1) cert maxs = false := by decide +kernel

/-- The value mutant: the CALL sends 2. -/
theorem mutantValue_fails : checkCF prog (codeOf 2 0x2a 2) cert maxs = false := by decide +kernel

/-- The code offset mutant: CODECOPY from offset 3. -/
theorem mutantOffset_fails : checkCF prog (codeOf 3 0x2a 1) cert maxs = false := by decide +kernel

/-- A certificate that says the program does not create covers no CALL, CREATE2 or CODECOPY. -/
theorem nocreates_fails : checkCF prog code { cert with creates := false } maxs = false := by
  decide +kernel

/-- Nor one that says it makes no call. -/
theorem nocalls_fails : checkCF prog code { cert with calls := false } maxs = false := by
  decide +kernel

/-- The gated checker of code with STATICCALLs takes no program that creates. -/
theorem gated_fails : checkCB prog code cert maxs = false := by decide +kernel

/-- The code offset read from the call data: the checker does not know it, so it refuses the
CODECOPY (SolarTV's code read takes its index as a word and would wrap where EthLib reads zeros). -/
def progDyn : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0x80)), .op (.stack (.push 8)), .op (.stack (.push 4)),
      .effect .calldataload 1, .op (.stack (.dup 2)), .effect .codecopy 3, .op (.stack (.push 0)),
      .op (.stack (.push 0)), .ret]] }

def codeDyn : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x08, 0x60, 0x04, 0x35, 0x82, 0x39, 0x5f, 0x5f, 0xf3]⟩

theorem dyn_fails : checkCF progDyn codeDyn { cert with costs := [9] } maxs = false := by
  decide +kernel

/-- With a pushed offset in place of the call data word the same shape passes, so `dyn_fails` fails at
the offset. -/
def progDynK : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0x80)), .op (.stack (.push 8)), .op (.stack (.push 4)),
      .op (.stack (.dup 2)), .effect .codecopy 3, .op (.stack (.push 0)),
      .op (.stack (.push 0)), .ret]] }

def codeDynK : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x08, 0x60, 0x04, 0x82, 0x39, 0x5f, 0x5f, 0xf3]⟩

theorem dynK_ok : checkCF progDynK codeDynK { cert with costs := [8] } maxs = true := by
  decide +kernel

/-- A known code offset of 2 ^ 32 is refused. -/
def progBig : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0x80)), .op (.stack (.push 8)),
      .op (.stack (.push (2 ^ 32))), .op (.stack (.dup 2)), .effect .codecopy 3,
      .op (.stack (.push 0)), .op (.stack (.push 0)), .ret]] }

def codeBig : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x08, 0x64, 0x01, 0x00, 0x00, 0x00, 0x00, 0x82, 0x39, 0x5f, 0x5f, 0xf3]⟩

theorem big_fails : checkCF progBig codeBig { cert with costs := [8] } maxs = false := by
  decide +kernel

/-- One below it passes, so `big_fails` fails at the offset. -/
def progSmall : Assemble.Program :=
  { blocks := [[.op (.stack (.push 0x80)), .op (.stack (.push 8)),
      .op (.stack (.push (2 ^ 32 - 1))), .op (.stack (.dup 2)), .effect .codecopy 3,
      .op (.stack (.push 0)), .op (.stack (.push 0)), .ret]] }

def codeSmall : ByteArray :=
  ⟨#[0x60, 0x80, 0x60, 0x08, 0x63, 0xff, 0xff, 0xff, 0xff, 0x82, 0x39, 0x5f, 0x5f, 0xf3]⟩

theorem small_ok : checkCF progSmall codeSmall { cert with costs := [8] } maxs = true := by
  decide +kernel

end SolidCore.Refinement.Solar.AssembleCreateExample
