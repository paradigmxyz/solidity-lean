import SolidCore.Refinement.Solar.AssembleCut
import SolidCore.Refinement.Solar.AssembleFast
import counter.gen.Counter.Evm5
import counter.gen.Counter.Bytecode

/-!
# Counter's bytecode runs as its final EVM IR, at every gas

solar's final EVM IR of `Counter` (`evm5`, freshly exported by the certify driver into
`Certified/counter/gen`) against the exported bytecode: the checker with GAS and memory at any
offset (`AssembleCut.checkC`) accepts it, so at every gas below `2 ^ 256` every result of the
bytecode is the EVM IR's or a failure that changes nothing (`bytecode_runs`). The certificate
is untrusted data from the asm-cert inference; the kernel's evaluation of `checkC` re-derives it.
Mutants of the bytecode (an altered SSTORE byte, an altered jump target) fail the check by
evaluation.
-/

namespace SolidCore.Refinement.Solar.CounterRun

open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleLoop
open SolidCore.Refinement.Solar.AssembleCut SolarTV.Export.Counter

/-- The exported runtime bytecode. -/
def code : ByteArray := ⟨(bytecode.map UInt8.ofNat).toArray⟩

def cert : Cert :=
  { offsets := [0x0, 0x34, 0x38, 0x41],
    needs := [0, 0, 1, 2],
    top := 2 ^ 140,
    turned := [],
    costs := [35, 3, 7, 9],
    types := [[], [], [some false], [some false, some false]],
    rets := [],
    env := false,
    reads := false }

def maxs : List Nat := [0, 1, 1, 2]

set_option maxRecDepth 100000 in
theorem walk_ok : (SolarTV.Assembly.walk (bytesOf code) cert.offset 0 (lower evm5 cert)).isSome =
    true := by
  have hw := walkS_drop (bytesOf code) cert.offset (lower evm5 cert) 0 (Nat.zero_le _)
  rw [List.drop_zero] at hw
  rw [← hw]
  decide +kernel

set_option maxRecDepth 100000 in
theorem blocks_ok : blocksOkC evm5 cert maxs 0 evm5.blocks = true := by
  decide +kernel

theorem labels_ok : labelsValid evm5 cert code = true :=
  labelsValid_of_walk walk_ok

theorem size_ok : code.size < 2 ^ 32 := by
  decide +kernel

theorem check_ok : checkC evm5 code cert maxs = true := by
  simp only [checkC, walk_ok, blocks_ok, labels_ok, decide_eq_true size_ok, Bool.and_true,
    Bool.true_and]
  decide

/-- **Counter's bytecode, run by run**: at every gas below `2 ^ 256` and every call, the oracle
of the run's table makes every result of the bytecode the final EVM IR's or a failure that changes
nothing. -/
theorem bytecode_runs (scope : SolarTV.Call → Prop) :
    WithinRunLt SolarTV.evmirSem (fun _ => evm5) code scope (RunOracle.CertOk cert) :=
  withinRun_of_checkC check_ok scope

/-- info: 'SolidCore.Refinement.Solar.CounterRun.bytecode_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytecode_runs

end SolidCore.Refinement.Solar.CounterRun
