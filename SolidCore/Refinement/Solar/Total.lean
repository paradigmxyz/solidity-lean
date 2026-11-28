import SolidCore.Refinement.Generic.Total
import SolidCore.Refinement.Keccak.TwoWords
import SolidCore.Refinement.Solar.Bank.Lowering
import SolidCore.Refinement.Solar.Events.Lowering

/-!
# bank and events: what makes their stages total

`Bank.certified` and `Events.certified` are stages from SolidCore to solar's bytecode under every
oracle `o` with EthLib's caller and hash (`Assemble.OracleOk o`). Two things could make such a
theorem hold for no reason: no oracle could satisfy its hypothesis, or SolidCore could finish no
call of its scope (a stage is vacuous there). This module rules out both:

* `ethOracle_sourceEnvOk`: an oracle with EthLib caller and Keccak-256 (the fields `Assemble.ethOracle`
  sets, for which `Assemble.ethOracle_ok` proves `Assemble.OracleOk`) is one the generic source
  stage takes (`Generic.SourceEnvOk`), since EthLib and SolidCore Keccak-256 agree on two words
  (`Keccak.ethKeccak_twoWords`).
* `Bank.defined`, `Events.defined`: SolidCore finishes every call of their scope (every function, any
  argument words, any storage, no value), from the generic stage's `Generic.defined`.
* `Bank.refines_of_stage`, `Events.refines_of_stage`: any stage from SolidCore to bytecode on that
  scope is therefore `Refines`, so
  `Bank.refines_of_stage hc (Bank.certified (Assemble.ethOracle o)
  (Assemble.ethOracle_ok o) Bank.ethKeccakAgree hc)` is the
  hypothesis-free total refinement of bank, and likewise for events.

The composition itself is not stated here: `Bank.certified` and `Events.certified` import the assembly
stage (`Solar/Assemble.lean`), which does not build against the pinned solar-tv.
-/

namespace SolidCore.Refinement.Solar

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

/-- The oracle with EthLib's caller and Keccak-256 and every other field constant: the fields
`Assemble.ethOracle` sets, on a constant oracle. -/
def ethOracle : SolarTV.Machine.Oracle :=
  { env := fun _ _ _ => 0, result := fun _ => 0, storageAfter := fun _ _ => 0,
    transientAfter := fun _ _ => 0,
    keccak := fun bytes => EthLib.Execution.Evm.keccak ⟨(bytes.map UInt8.ofBitVec).toArray⟩,
    caller := BitVec.ofNat 160 SolidCore.Refinement.callerAddress }

/-- It is one the generic source stage takes: its caller is SolidCore's and its Keccak-256 of two
words is SolidCore's slot hash. So the source stages' oracle hypothesis is satisfiable. -/
theorem ethOracle_sourceEnvOk : Generic.SourceEnvOk ethOracle :=
  ⟨by unfold Generic.CallerOk; decide +kernel,
    fun a b _ _ => Keccak.ethKeccak_twoWords a b⟩

theorem sourceEnvOk_exists : ∃ o, Generic.SourceEnvOk o := ⟨ethOracle, ethOracle_sourceEnvOk⟩

namespace Bank

/-- SolidCore finishes every call of `deposit`, `depositFor` and `balanceOf` on any argument
words, no value, from any storage. -/
theorem defined {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.defined hd (by rw [hk]; exact check_stage0)

/-- A stage from bank's SolidCore contract to any bytecode on that scope is a total refinement. -/
theorem refines_of_stage {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {code : ByteArray}
    (st : Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call)) :
    Refines fuel c code (fun call => ∃ σ, fullScope fns σ call) :=
  refines_iff_total.mpr (total_iff_stage.mpr ⟨st, defined hc⟩)

end Bank

namespace Events

/-- SolidCore finishes every call of `transfer` on any argument words, no value, from any storage. -/
theorem defined {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ, fullScope fns σ call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.defined hd (by rw [hk]; exact check_stage0)

/-- A stage from events' SolidCore contract to any bytecode on that scope is a total
refinement. -/
theorem refines_of_stage {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {code : ByteArray}
    (st : Stage (solidCore fuel) ethLib c code (fun call => ∃ σ, fullScope fns σ call)) :
    Refines fuel c code (fun call => ∃ σ, fullScope fns σ call) :=
  refines_iff_total.mpr (total_iff_stage.mpr ⟨st, defined hc⟩)

end Events

/-- info: 'SolidCore.Refinement.Solar.ethOracle_sourceEnvOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ethOracle_sourceEnvOk

/--
info: 'SolidCore.Refinement.Solar.Bank.refines_of_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Bank.refines_of_stage

/--
info: 'SolidCore.Refinement.Solar.Events.refines_of_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Events.refines_of_stage

end SolidCore.Refinement.Solar
