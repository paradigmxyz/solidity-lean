import SolidCore.Refinement.Solar.AssembleCut
import SolidCore.Refinement.Solar.AssembleFast
import arraymax.gen.ArrayMaxEntry.Evm15
import arraymax.gen.ArrayMaxEntry.Bytecode

/-!
# ArrayMaxEntry's bytecode runs as its final EVM IR

solar's final EVM IR of `ArrayMaxEntry` (`evm15`) loads at computed offsets (the array's
elements in memory) and copies call data of the array's length; the checker with memory at any
offset (`AssembleCut.checkC`) accepts its bytecode, so at every gas below `2 ^ 256` every result
of the bytecode is the EVM IR's or a failure that changes nothing. The bytecode with CODECOPY in
place of its CALLDATACOPY (byte 148) is rejected by evaluation.
-/

namespace SolidCore.Refinement.Solar.ArrayMaxRun

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolarTV.Export.ArrayMaxEntry

def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

/-- The same bytecode with CODECOPY (0x39) in place of the CALLDATACOPY at byte 148. -/
def mutant : ByteArray := ⟨((bytecode.set 148 0x39).map UInt8.ofNat).toArray⟩

def cert : Cert :=
  { offsets := [0x0, 0x13, 0x17, 0x2c, 0xbc, 0xed, 0x10e, 0x124, 0x13c, 0x151, 0x16c, 0x181, 0x1b6, 0x1d0, 0x1e8, 0x1ff, 0x219, 0x236, 0x253, 0x268],
    needs := [0, 0, 8, 1, 9, 7, 9, 4, 3, 12, 13, 11, 13, 13, 11, 10, 10, 10, 8, 7],
    top := 2 ^ 140,
    turned := [],
    costs := [12, 3, 5, 112, 40, 26, 8, 14, 5, 11, 5, 43, 10, 8, 7, 10, 13, 13, 5, 9],
    types := [[], [],
      List.replicate 8 (some false), [some false], List.replicate 9 (some false),
      List.replicate 7 (some false), List.replicate 9 (some false), List.replicate 4 (some false),
      List.replicate 3 (some false), List.replicate 12 (some false), List.replicate 13 (some false),
      List.replicate 11 (some false), List.replicate 13 (some false), List.replicate 13 (some false),
      List.replicate 11 (some false), List.replicate 10 (some false), List.replicate 10 (some false),
      List.replicate 10 (some false), List.replicate 8 (some false), List.replicate 7 (some false)],
    rets := [],
    env := false,
    reads := false }

def maxs : List Nat := [0, 6, 8, 1, 9, 7, 9, 15, 3, 12, 13, 11, 13, 13, 11, 10, 10, 10, 8, 7]

set_option maxRecDepth 100000 in
theorem walk_ok : (SolarTV.Assembly.walk (bytesOf code) cert.offset 0 (lower evm15 cert)).isSome =
    true := by
  have hw := walkS_drop (bytesOf code) cert.offset (lower evm15 cert) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  rw [← hw]
  decide +kernel

set_option maxRecDepth 100000 in
theorem blocks_ok : blocksOkC evm15 cert maxs 0 evm15.blocks = true := by
  decide +kernel

theorem labels_ok : labelsValid evm15 cert code = true :=
  labelsValid_of_walk walk_ok

theorem size_ok : code.size < 2 ^ 32 := by
  decide +kernel

theorem check_ok : checkC evm15 code cert maxs = true := by
  simp only [checkC, walk_ok, blocks_ok, labels_ok, decide_eq_true size_ok, Bool.and_true,
    Bool.true_and]
  decide

set_option maxRecDepth 100000 in
/-- The mutant fails the check by evaluation. -/
theorem mutant_fails : checkC evm15 mutant cert maxs = false := by
  decide +kernel

/-- **ArrayMaxEntry's bytecode, run by run**: at every gas below `2 ^ 256` and every call, the
oracle of the run's table makes every result of the bytecode the final EVM IR's or a failure that
changes nothing. -/
theorem bytecode_runs (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => evm15) code scope (RunOracle.CertOk cert) :=
  withinRun_of_checkC check_ok scope

/-- info: 'SolidCore.Refinement.Solar.ArrayMaxRun.bytecode_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode_runs

end SolidCore.Refinement.Solar.ArrayMaxRun
