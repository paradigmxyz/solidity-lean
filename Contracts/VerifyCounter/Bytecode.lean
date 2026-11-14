import Contracts.VerifyCounter.Holds
import Contracts.VerifyCounter.Bump
import verify_counter.Proofs.Stages
import Contracts.VerifyCounter.Assembly
import SolidCore.Refinement.Solar.EndToEnd

/-!
# solar-verify's Counter: its specification holds of its bytecode at every gas

The composition, with no hypotheses: solar-verify's specification of Counter (`spec`: the
invariant `count <= limit` and all five functions, `bump`'s loop included) holds of the 496 bytes
of runtime bytecode solar compiled (`code`, bound to `manifest` by `bound`) at every gas.

* `Mir.holds_of_certified`: the specification holds of the first lowered MIR (`holds_stage0`, with
  `bump`'s loop by its cut points) and is carried to the final EVM IR along solar-tv's backend
  stages read backwards (`verify_counter_certified_back`).
* `VerifyCounterAsm.assembly`: the assembly stage of looping code, at every gas: every result of
  the bytecode is the final EVM IR's or a failure that changes nothing
  (`AssembleLoop.within_of_checkL` at the kernel's evaluation of the checker).
* `Final.Holds.of_within` composes them.

`evm11_bump_post` and `evm11_bump_ends`: on the final EVM IR, every call of `bump` ends, and its
end meets bump's postcondition. `loopTarget_rejected`: the bytecode whose loop jumps back to the
wrong block is rejected by the checker, by a mismatch of the walk.
-/

namespace SolidCore.Refinement.Solar.VerifyCounter

open SolarTV SolarTV.Machine SolidCore.Refinement.Final

/-- bump's postcondition on the final EVM IR, on every call of bump, under every oracle. -/
theorem evm11_bump_post (o : Oracle) (call : Call) (hsel : Milestone.VerifyCounter.Bump.IsBump call)
    (r : Halt × Machine.State) (e : EVM.Program.layer.Ends o SolarTV.Export.Counter.evm11 call r) :
    Milestone.VerifyCounter.Bump.Post call r :=
  Milestone.VerifyCounter.Bump.post_of_certified o
    (Milestone.VerifyCounter.verify_counter_certified_back o) call hsel r e

/-- Every call of bump ends on the final EVM IR, and meets bump's postcondition. -/
theorem evm11_bump_ends (o : Oracle) (call : Call) (hsel : Milestone.VerifyCounter.Bump.IsBump call) :
    ∃ r, EVM.Program.layer.Ends o SolarTV.Export.Counter.evm11 call r ∧
      Milestone.VerifyCounter.Bump.Post call r :=
  Milestone.VerifyCounter.Bump.ends_of_certified o
    (Milestone.VerifyCounter.verify_counter_certified o) call hsel

/-- An oracle. The EVM IR's specification holds under every one, and the bytecode reads none. -/
def anyOracle : Oracle :=
  ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, 0⟩

open EthLib.Execution.Evm.Logic in
/-- The bytes of a code stored in a number, by the number's bytes. -/
theorem toList_ofNat (n size : Nat) :
    (NatCode.ofNat n size).data.toList = (List.range size).map (NatCode.natByte n size) := by
  apply List.ext_getElem <;> simp [NatCode.ofNat]

/-- Two codes with the same bytes are the same. -/
theorem bytesOf_inj {a b : ByteArray} (h : Assemble.bytesOf a = Assemble.bytesOf b) : a = b := by
  have h' : a.data.toList = b.data.toList :=
    (List.map_injective_iff.2 (fun x y hxy => UInt8.toNat_inj.1 hxy)) h
  cases a; cases b
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.1 h'

open EthLib.Execution.Evm.Logic in
/-- `runtimeNat`'s 496 bytes are the bytecode solar exported with its stages. -/
theorem runtime_bytes : (List.range 496).map (fun i => (NatCode.natByte runtimeNat 496 i).toNat) =
    SolarTV.Export.Counter.bytecode := by
  decide +kernel

/-- The assembly stage's bytes are the exported bytecode. -/
theorem asm_bytes : Assemble.bytesOf VerifyCounterAsm.code = SolarTV.Export.Counter.bytecode := by
  decide +kernel

/-- The bytecode of the assembly stage is `code`, bound to the manifest (`bound`). -/
theorem asm_code_eq : VerifyCounterAsm.code = code := by
  apply bytesOf_inj
  rw [asm_bytes]
  unfold Assemble.bytesOf code
  rw [toList_ofNat, List.map_map]
  exact runtime_bytes.symm

/-- The specification holds of the final EVM IR. -/
theorem holds_evm11 (o : Oracle) : Holds (SolarTV.evmirSem o) SolarTV.Export.Counter.evm11 spec :=
  Mir.holds_of_certified o (Milestone.VerifyCounter.verify_counter_certified_back o)

/-- **solar-verify's specification of Counter holds of its bytecode at every gas**, every function,
`bump`'s loop included, with no hypotheses. -/
theorem spec_holds_of_bytecode (gas : Nat) : Holds (ethLibWith gas) code spec := by
  rw [← asm_code_eq]
  exact (holds_evm11 anyOracle).of_within (VerifyCounterAsm.assembly anyOracle spec.Calls gas)

/-- The same theorem by the generic composition (`EndToEnd.holds_of_checkL`) that generated proofs
use: the specification on stage0, solar-tv's backend stages read backwards, and the checker of code
with loops. -/
theorem spec_holds_of_bytecode_generic (gas : Nat) : Holds (ethLibWith gas) code spec := by
  rw [← asm_code_eq]
  exact EndToEnd.holds_of_checkL (Mir.holds_stage0 anyOracle)
    (Milestone.VerifyCounter.verify_counter_certified_back anyOracle) (fun _ _ => trivial)
    VerifyCounterAsm.check_ok (fun h => absurd h (by decide)) gas

/-- The bytecode whose loop jumps back to block 7's JUMPDEST in place of block 8's is rejected. -/
theorem loopTarget_rejected :
    AssembleLoop.checkL SolarTV.Export.Counter.evm11 VerifyCounterAsm.loopTargetCode
      VerifyCounterAsm.cert VerifyCounterAsm.maxs = false :=
  VerifyCounterAsm.loopTarget_check

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.spec_holds_of_bytecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spec_holds_of_bytecode

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.evm11_bump_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evm11_bump_post

/-- info: 'SolidCore.Refinement.Solar.VerifyCounter.evm11_bump_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evm11_bump_ends

end SolidCore.Refinement.Solar.VerifyCounter
