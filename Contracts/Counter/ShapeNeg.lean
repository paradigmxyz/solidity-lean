import Contracts.Counter.Shape

/-!
# Counter's negative controls

Each mutant fails to reach any status by the kernel's evaluation or by a mismatch, never by a
timeout:

* bytecode mutants (`checkC` rejects each, and the published binding to the exported hex fails
  for each): `ADD` turned into `SUB` (byte 42), the overflow branch's jump target moved to
  `get`'s block (byte 47), the `SSTORE` dropped for a `POP` (byte 50), `STOP` turned into
  `SELFDESTRUCT`, an opcode outside the supported set (byte 51);
* the wrong postcondition `x == old(x) + d + 1` is not met by SolidCore's `Counter`
  (`wrong_spec_not_meets`, on `inc(1)` from the empty storage);
* a gas bound of `2 ^ 64` or more is no bound: `Shapes.Certified` with it is refuted outright
  (`not_certified_unbounded`).
-/

namespace SolidCore.Refinement.Solar.Counter.ShapeNeg

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar.Assemble SolidCore.Refinement.Solar.AssembleCut
open SolidCore.Refinement.Solar.Counter.Shape SolidCore.Refinement.Solar.Counter.ShapeSpec SolidCore.Refinement.Solar.Counter.Final
open SolidCore.Refinement.Solar.CounterRun (cert maxs)
open SolidCore.Refinement.Evm.Wide EthLib.Base

/-- The exported bytecode with byte `i` replaced by `b`. -/
def mutant (i b : Nat) : ByteArray :=
  ⟨((SolarTV.Export.Counter.bytecode.set i b).map UInt8.ofNat).toArray⟩

set_option maxRecDepth 100000

theorem add_to_sub : checkC SolarTV.Export.Counter.evm5 (mutant 42 0x03) cert maxs = false := by
  decide +kernel

theorem jump_moved : checkC SolarTV.Export.Counter.evm5 (mutant 47 0x38) cert maxs = false := by
  decide +kernel

theorem sstore_dropped : checkC SolarTV.Export.Counter.evm5 (mutant 50 0x50) cert maxs = false := by
  decide +kernel

theorem unsupported_opcode :
    checkC SolarTV.Export.Counter.evm5 (mutant 51 0xff) cert maxs = false := by
  decide +kernel

/-- The binding of the published statement fails for every mutant. -/
theorem binding_fails :
    (([42, 47, 50, 51].zip [0x03, 0x38, 0x50, 0xff]).all fun ib =>
      hexOf ((mutant ib.1 ib.2).data.toList.map (·.toNat)) != SolarTV.Export.Counter.Manifest.bytecodeHex)
      = true := by
  decide +kernel

/-- `inc(d)` with the postcondition `x == old(x) + d + 1`. -/
def wrongInc : FnSpec Nat := { incSpec with ensures := fun args x x' out => x' = x + args.headD 0 + 1 ∧ out = [] }

def wrongSpec : ContractSpec Nat := { cspec with fns := [wrongInc, getSpec] }

theorem wrong_spec_not_meets {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    ¬Shapes.Meets (solidCore fuel) c cspec.Calls (Shapes.specPost wrongSpec) := by
  have hcall : cspec.Calls (incSpec.call [1] 0 []) :=
    ⟨incSpec, by simp [cspec, SolidCore.Refinement.Solar.Counter.Final.spec], [1], .cons (by decide) .nil,
      0, by decide, [], rfl⟩
  refine Shapes.not_meets_of hcall (source_run_every hc _ (calls_every hcall)) ?_
  intro h
  have := h wrongInc (by simp [wrongSpec]) [1] (.cons (by decide) .nil) 0 (by decide) [] rfl trivial
    trivial
  rw [inc_call 1 0 (by decide)] at this
  have hcall' : ({ callOf incSelector [BitVec.ofNat 256 1] with callvalue := 0, storage := [] } : Call) =
      { callOf incSelector [BitVec.ofNat 256 1] with storage := [] } := rfl
  rw [hcall', expectedEvery_inc] at this
  have h1 := (this.1 (by decide)).1.1
  revert h1
  decide

/-- The strongest status needs a gas bound below `2 ^ 64`: an unbounded claim is refuted. -/
theorem not_certified_unbounded {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    {A P : Call → Observable → Prop} :
    ¬Shapes.Certified (solidCore fuel) c CounterRun.code cspec.Calls A P (fun _ => 2 ^ 64) := by
  intro h
  obtain ⟨call, hc⟩ := h.inhabited
  exact Shapes.not_resources_of_bound hc (le_refl _) h.resources

end SolidCore.Refinement.Solar.Counter.ShapeNeg
