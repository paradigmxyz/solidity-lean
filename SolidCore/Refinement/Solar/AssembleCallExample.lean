import SolidCore.Refinement.Solar.AssembleCallSeg

/-!
# A STATICCALL to an address the call names: an example and mutants

A program that makes a STATICCALL with all its gas to the address in the call data's word at
offset 4, with no input and 32 bytes of output at offset 0, then stores the call's flag at offset 0
and returns that word. The checker without the no-call gate (`AssembleCut.checkCB`) accepts the
bytecode under a certificate that says the program makes calls; at every gas below `2 ^ 256`, every
run that meets the named hypotheses (`AssembleCallSeg.StaticRunner`, `AssembleCallSeg.CalleesRun`)
gives the program's result under the oracle of the run's table, which agrees with an open world.

Rejected by evaluation: the bytecode reading the address at offset 5, the bytecode with
DELEGATECALL in place of STATICCALL, the certificate that says the program makes no call, and the
gated checker `AssembleCut.checkC` (programs without calls only).
-/

namespace SolidCore.Refinement.Solar.AssembleCallExample

open SolidCore.Refinement.Solar SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolidCore.Refinement.Solar.AssembleCallSeg
open SolidCore.Refinement.Final

/-- PUSH1 32, PUSH0 x3, PUSH1 4 CALLDATALOAD, GAS, STATICCALL, then the flag stored at offset 0
and returned. -/
def prog : Assemble.Program :=
  { blocks := [[.op (.stack (.push 32)), .op (.stack (.push 0)), .op (.stack (.push 0)),
      .op (.stack (.push 0)), .op (.stack (.push 4)), .effect .calldataload 1, .effect .gas 0,
      .effect (.call .staticcall) 6, .op (.stack (.push 0)), .op .store, .op (.stack (.push 32)),
      .op (.stack (.push 0)), .ret]] }

def code : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

/-- The address read from the call data at offset 5. -/
def mutantAddr : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x05, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

/-- DELEGATECALL (0xf4) in place of STATICCALL. -/
def mutantKind : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xf4, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def cert : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [13], types := [[]], calls := true }

def maxs : List Nat := [0]

theorem check_ok : checkCB prog code cert maxs = true := by decide +kernel

theorem mutantAddr_fails : checkCB prog mutantAddr cert maxs = false := by decide +kernel

theorem mutantKind_fails : checkCB prog mutantKind cert maxs = false := by decide +kernel

/-- A certificate that says the program makes no call does not cover the STATICCALL. -/
theorem nocalls_fails : checkCB prog code { cert with calls := false } maxs = false := by
  decide +kernel

/-- The gated checker takes programs without calls only. -/
theorem gated_fails : checkC prog code cert maxs = false := by decide +kernel

/-- **At every gas below `2 ^ 256`, every result of the bytecode is the program's**, under an oracle
that agrees with an open world, for every run meeting the named hypotheses. -/
theorem bytecode (codes : SolidCore.Solidity.Shared.Account.BytesMap) (scope : SolarTV.Call → Prop)
    (hP : ∀ gas, StaticRunner gas) (hQ : ∀ gas call, scope call → CalleesRun gas code call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : SolarTV.Machine.Oracle) (W : World),
      W.Open ∧ SolidCore.Refinement.CallsAgree o W ∧ RunOracle.CertOk cert o ∧
      SolidCore.Refinement.Final.Within (SolarTV.evmirSem o) (ethLibWith gas) prog code (· = call) :=
  assembly_of_checkCB check_ok codes scope hP hQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCallExample.bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode

/-- The flag and RETURNDATASIZE, after the call, stored at offsets 0 and 32 and returned. -/
def progRds : Assemble.Program :=
  { blocks := [[.op (.stack (.push 32)), .op (.stack (.push 0)), .op (.stack (.push 0)),
      .op (.stack (.push 0)), .op (.stack (.push 4)), .effect .calldataload 1, .effect .gas 0,
      .effect (.call .staticcall) 6, .op (.stack (.push 0)), .op .store, .effect .returndatasize 0,
      .op (.stack (.push 32)), .op .store, .op (.stack (.push 64)), .op (.stack (.push 0)), .ret]] }

def codeRds : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x3d, 0x60, 0x20, 0x52,
    0x60, 0x40, 0x5f, 0xf3]⟩

/-- CALLDATASIZE (0x36) in place of RETURNDATASIZE. -/
def mutantRds : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x36, 0x60, 0x20, 0x52,
    0x60, 0x40, 0x5f, 0xf3]⟩

def certRds : Assemble.Cert := { cert with costs := [16] }

theorem checkRds_ok : checkCB progRds codeRds certRds maxs = true := by decide +kernel

theorem mutantRds_fails : checkCB progRds mutantRds certRds maxs = false := by decide +kernel

/-- **The callee's return data size, read back**: at every gas below `2 ^ 256`, every result of the
bytecode is the program's, whose RETURNDATASIZE reads the table's output of the call. -/
theorem bytecodeRds (codes : SolidCore.Solidity.Shared.Account.BytesMap) (scope : SolarTV.Call → Prop)
    (hP : ∀ gas, StaticRunner gas) (hQ : ∀ gas call, scope call → CalleesRun gas codeRds call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : SolarTV.Machine.Oracle) (W : World),
      W.Open ∧ SolidCore.Refinement.CallsAgree o W ∧ RunOracle.CertOk certRds o ∧
      SolidCore.Refinement.Final.Within (SolarTV.evmirSem o) (ethLibWith gas) progRds codeRds
        (· = call) :=
  assembly_of_checkCB checkRds_ok codes scope hP hQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCallExample.bytecodeRds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeRds

/-- After the call, the whole return data copied to offset 0 and returned: RETURNDATASIZE PUSH0
PUSH0 RETURNDATACOPY RETURNDATASIZE PUSH0 RETURN. -/
def progRdc : Assemble.Program :=
  { blocks := [[.op (.stack (.push 32)), .op (.stack (.push 0)), .op (.stack (.push 0)),
      .op (.stack (.push 0)), .op (.stack (.push 4)), .effect .calldataload 1, .effect .gas 0,
      .effect (.call .staticcall) 6, .op (.stack (.push 0)), .op .store, .effect .returndatasize 0,
      .op (.stack (.push 0)), .op (.stack (.push 0)), .effect .returndatacopy 3,
      .effect .returndatasize 0, .op (.stack (.push 0)), .ret]] }

def codeRdc : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x3d, 0x5f, 0x5f, 0x3e,
    0x3d, 0x5f, 0xf3]⟩

/-- CODECOPY (0x39) in place of RETURNDATACOPY. -/
def mutantRdc : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x35, 0x5a, 0xfa, 0x5f, 0x52, 0x3d, 0x5f, 0x5f, 0x39,
    0x3d, 0x5f, 0xf3]⟩

def certRdc : Assemble.Cert := { cert with costs := [17] }

theorem checkRdc_ok : checkCB progRdc codeRdc certRdc maxs = true := by decide +kernel

theorem mutantRdc_fails : checkCB progRdc mutantRdc certRdc maxs = false := by decide +kernel

/-- **The callee's return data, copied and returned**: return data bubbling. At every gas below
`2 ^ 256`, every result of the bytecode is the program's. -/
theorem bytecodeRdc (codes : SolidCore.Solidity.Shared.Account.BytesMap) (scope : SolarTV.Call → Prop)
    (hP : ∀ gas, StaticRunner gas) (hQ : ∀ gas call, scope call → CalleesRun gas codeRdc call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : SolarTV.Machine.Oracle) (W : World),
      W.Open ∧ SolidCore.Refinement.CallsAgree o W ∧ RunOracle.CertOk certRdc o ∧
      SolidCore.Refinement.Final.Within (SolarTV.evmirSem o) (ethLibWith gas) progRdc codeRdc
        (· = call) :=
  assembly_of_checkCB checkRdc_ok codes scope hP hQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCallExample.bytecodeRdc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeRdc


/-! ## A STATICCALL to ECRECOVER -/

/-- PUSH1 32, PUSH0, PUSH1 128, PUSH0, PUSH1 1, GAS, STATICCALL: ECRECOVER on the 128 bytes of
memory at 0, its 32-byte output written at 0; the flag stored at 64, and the output returned. -/
def progEc : Assemble.Program :=
  { blocks := [[.op (.stack (.push 32)), .op (.stack (.push 0)), .op (.stack (.push 128)),
      .op (.stack (.push 0)), .op (.stack (.push 1)), .effect .gas 0,
      .effect (.call .staticcall) 6, .op (.stack (.push 64)), .op .store, .op (.stack (.push 32)),
      .op (.stack (.push 0)), .ret]] }

def codeEc : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x60, 0x80, 0x5f, 0x60, 0x01, 0x5a, 0xfa, 0x60, 0x40, 0x52, 0x60, 0x20, 0x5f,
    0xf3]⟩

/-- The STATICCALL to address 2 (SHA-256) in place of ECRECOVER. -/
def mutantEcAddr : ByteArray :=
  ⟨#[0x60, 0x20, 0x5f, 0x60, 0x80, 0x5f, 0x60, 0x02, 0x5a, 0xfa, 0x60, 0x40, 0x52, 0x60, 0x20, 0x5f,
    0xf3]⟩

def certEc : Assemble.Cert :=
  { offsets := [0], needs := [0], top := 2 ^ 140, costs := [12], types := [[]], calls := true }

theorem checkEc_ok : checkCB progEc codeEc certEc maxs = true := by decide +kernel

theorem mutantEcAddr_fails : checkCB progEc mutantEcAddr certEc maxs = false := by decide +kernel

/-- **The ECRECOVER bytecode, at every gas below `2 ^ 256`**: every result is the program's
under an oracle that agrees with an open world, in which the call to address 1 is answered by the
source's ECRECOVER; `CalleesRun` admits the call through `AssembleCallCut.PreOk`, which names
`AssembleCallPre.EcrecoverAgree`. -/
theorem bytecodeEc (codes : SolidCore.Solidity.Shared.Account.BytesMap)
    (scope : SolarTV.Call → Prop) (hP : ∀ gas, StaticRunner gas)
    (hQ : ∀ gas call, scope call → CalleesRun gas codeEc call) :
    ∀ gas, gas < 2 ^ 256 → ∀ call, scope call → ∃ (o : SolarTV.Machine.Oracle) (W : World),
      W.Open ∧ SolidCore.Refinement.CallsAgree o W ∧ RunOracle.CertOk certEc o ∧
      SolidCore.Refinement.Final.Within (SolarTV.evmirSem o) (ethLibWith gas) progEc codeEc (· = call) :=
  assembly_of_checkCB checkEc_ok codes scope hP hQ

/-- info: 'SolidCore.Refinement.Solar.AssembleCallExample.bytecodeEc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecodeEc

end SolidCore.Refinement.Solar.AssembleCallExample
