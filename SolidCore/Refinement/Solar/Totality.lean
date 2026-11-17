import SolidCore.Refinement.Generic.DefinedValue
import SolidCore.Refinement.Solar.Total
import SolidCore.Refinement.Solar.Bank.Certified
import SolidCore.Refinement.Solar.Events.Certified
import SolidCore.Refinement.Solar.MulX.Certified

/-!
# bank, events and mulx: SolidCore ends, so the certified stages are total

`Bank.certified`, `Events.certified` and `MulX.certified_*` are stages: if SolidCore finishes a
call of the scope within its fuel (4096 statements), the bytecode gives the same observable. A
stage says nothing on a call SolidCore does not finish (`Stage.of_never`), so on their own they
could hold because SolidCore ends on no call. This module closes that gap for the three
contracts, as `counter` and `c4` already do:

* `<C>.source_ends` (and `source_ends_value`, `source_ends_at`, `source_ends_at_value` where the
  certified theorems have those scopes): SolidCore finishes every call of the scope within fuel
  `<C>.fuel = 4096`, read off the generic source stage's check (`Generic.definedAt`, and
  `Generic.definedAtValue` in Generic/DefinedValue.lean for calls with a value, which SolidCore rejects).
* `<C>.certified_total` (and the other scopes): the end-to-end statement as `Refines`, a total
  refinement (`Total (solidCore fuel) ethLib`): on every call of the scope both SolidCore and the
  bytecode under EthLib finish, with the same observable, so every behaviour of the bytecode
  there is SolidCore's (`Refines.backward`). Each is `bytecode_total_of_stages` applied to the
  source stage, solar-tv's backend stages and the assembly stage, with the specification
  "SolidCore ends" (`satisfies_of_defined`); no oracle hypothesis is left, since the stages hold
  under `Assemble.ethOracle o` for any `o`.
* `<C>.scope_inhabited`: each scope has a call, so none of these statements is vacuous.
* `Generic.not_defined_of_none`, `not_refines_of_none`: a scope with a call on which SolidCore
  returns nothing refutes `Defined` and `Refines` (running out of fuel is a failure of the
  theorem, never a vacuous success).
* `<C>.not_source_ends_two`, `<C>.not_certified_total_two`: the negatives. With fuel 2 SolidCore
  returns nothing on the scope's `probeCall` (`run2_eq`, the kernel's evaluation; with fuel 3 it
  finishes), so `source_ends` and `certified_total` fail at fuel 2, by mismatch.

No sorry, native_decide or bv_decide: the theorems depend on propext, Classical.choice and
Quot.sound only (pinned below).
-/

namespace SolidCore.Refinement.Solar

open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Solidity

namespace Bank

/-- The fuel the statements are at. -/
theorem fuel_eq : fuel = 4096 := rfl

/-- **SolidCore's `Bank` ends**: every call of `deposit`, `depositFor` and `balanceOf` on any
argument words, no value, from any storage, finishes within fuel 4096. -/
theorem source_ends {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ, fullScope fns σ call) :=
  defined hc

/-- **SolidCore's `Bank` ends at every value**: with a value it reverts, so it finishes too. -/
theorem source_ends_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.definedValue hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- **Bank, SolidCore to solar's bytecode, total**: on every call of `deposit`, `depositFor` and
`balanceOf` on any argument words, no value, from any storage, SolidCore and the bytecode under
EthLib both finish, with the same observable. -/
theorem certified_total {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fun call => ∃ σ, fullScope fns σ call) :=
  let o := Assemble.ethOracle ethOracle
  let ho := Assemble.ethOracle_ok ethOracle
  Generic.refines_of_defined_stages (source_ends hc)
    (lowering o (sourceEnvOk_of o ho ethKeccakAgree) hc)
    (fun call _ => SolarTV.Milestone.Bank.bank_mir_to_evmir o call trivial) (stageOk o ho _)

/-- **Bank, total at every value**. -/
theorem certified_total_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  let o := Assemble.ethOracle ethOracle
  let ho := Assemble.ethOracle_ok ethOracle
  Generic.refines_of_defined_stages (source_ends_value hc)
    (loweringValue o (sourceEnvOk_of o ho ethKeccakAgree) hc)
    (fun call _ => SolarTV.Milestone.Bank.bank_mir_to_evmir o call trivial) (stageOk o ho _)

/-- The scope has a call (`balanceOf(0)` from empty storage): `certified_total` is not vacuous. -/
theorem scope_inhabited : ∃ call, ∃ σ, fullScope fns σ call :=
  ⟨_, [], fnBalanceOf, by simp [fns], [0], rfl, by simp, rfl⟩

end Bank

namespace Events

theorem fuel_eq : fuel = 4096 := rfl

/-- **SolidCore's `Events` ends**: every call of `transfer` on any argument words, no value, from
any storage, finishes within fuel 4096. -/
theorem source_ends {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ, fullScope fns σ call) :=
  defined hc

/-- **SolidCore's `Events` ends at every value**. -/
theorem source_ends_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact Generic.definedValue hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0)

/-- **Events, SolidCore to solar's bytecode, total**: on every call of `transfer` on any argument
words, no value, from any storage, SolidCore and the bytecode under EthLib both finish, with the
same observable. -/
theorem certified_total {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fun call => ∃ σ, fullScope fns σ call) :=
  let o := Assemble.ethOracle ethOracle
  let ho := Assemble.ethOracle_ok ethOracle
  Generic.refines_of_defined_stages (source_ends hc) (lowering o (callerOk_of o ho) hc)
    (fun call _ => SolarTV.Milestone.Events.events_mir_to_evmir o call trivial) (stageOk o ho _)

/-- **Events, total at every value**. -/
theorem certified_total_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fun call => ∃ σ v, Generic.fullScopeValue fns σ v call) :=
  let o := Assemble.ethOracle ethOracle
  let ho := Assemble.ethOracle_ok ethOracle
  Generic.refines_of_defined_stages (source_ends_value hc) (loweringValue o (callerOk_of o ho) hc)
    (fun call _ => SolarTV.Milestone.Events.events_mir_to_evmir o call trivial) (stageOk o ho _)

/-- The scope has a call (`transfer(0, 0)` from empty storage). -/
theorem scope_inhabited : ∃ call, ∃ σ, fullScope fns σ call :=
  ⟨_, [], fnTransfer, by simp [fns], [0, 0], rfl, by simp, rfl⟩

end Events

namespace MulX

open SolarTV.Export.Main

theorem fuel_eq : fuel = 4096 := rfl

/-- **SolidCore's `Main` ends from the deployed storage**: every call of `m` and `n` on any
argument words, no value, from the storage the constructor leaves, finishes within fuel 4096. -/
theorem source_ends {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fullScope fns deployed) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact fun call h => Generic.definedAt hd (by rw [hk]; exact check_stage0) call
    ⟨deployed, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- **SolidCore's `Main` ends from any storage that writes slot 0**. -/
theorem source_ends_at {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c scopeAt := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  rintro call ⟨σ, ⟨kv, hkv, h0⟩, hs⟩
  refine Generic.definedAt hd (by rw [hk]; exact check_stage0) call ⟨σ, ?_, hs⟩
  intro kv' hkv'
  simp only [deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

/-- **SolidCore's `Main` ends from the deployed storage at every value**. -/
theorem source_ends_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c (fun call => ∃ v, Generic.fullScopeValue fns deployed v call) := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  exact fun call ⟨v, h⟩ => Generic.definedAtValue hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0) call ⟨deployed, v, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- **SolidCore's `Main` ends from any storage that writes slot 0 at every value**. -/
theorem source_ends_at_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Defined (solidCore fuel) c scopeAtValue := by
  obtain ⟨hk, d, hd⟩ := deployed_of hc
  rintro call ⟨σ, v, ⟨kv, hkv, h0⟩, hs⟩
  refine Generic.definedAtValue hd (by rw [hk]; exact check_stage0)
    (by rw [hk]; exact checkValue_stage0) call ⟨σ, v, ?_, hs⟩
  intro kv' hkv'
  simp only [deployed, List.mem_singleton] at hkv'
  subst hkv'
  exact ⟨kv, hkv, h0⟩

/-- The backend stages from stage0 to evm8, on any scope. -/
theorem mirToEvmir (o : SolarTV.Machine.Oracle) (scope : SolarTV.Call → Prop) :
    SolarTV.Stage (SolarTV.mirSem o) (SolarTV.evmirSem o) stage0 evm8 scope :=
  (SolarTV.Milestone.Mulx.mulx_mir_to_evmir o).mono fun _ _ => trivial

/-- **mulx, SolidCore to solar's bytecode, total, from the deployed storage**: on every call of `m`
and `n` on any argument words, no value, from the storage the constructor leaves, SolidCore and
the bytecode under EthLib both finish, with the same observable. -/
theorem certified_total {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fullScope fns deployed) :=
  let o : SolarTV.Machine.Oracle := Solar.ethOracle
  Generic.refines_of_defined_stages (source_ends hc) (lowering o hc) (mirToEvmir o _)
    (stageAll o _)

/-- **mulx, total, from any storage that writes slot 0**. -/
theorem certified_total_at {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code scopeAt :=
  let o : SolarTV.Machine.Oracle := Solar.ethOracle
  Generic.refines_of_defined_stages (source_ends_at hc) (loweringAt o hc) (mirToEvmir o _)
    (stageAll o _)

/-- **mulx, total, from the deployed storage at every value**. -/
theorem certified_total_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code (fun call => ∃ v, Generic.fullScopeValue fns deployed v call) :=
  let o : SolarTV.Machine.Oracle := Solar.ethOracle
  Generic.refines_of_defined_stages (source_ends_value hc) (loweringValue o hc) (mirToEvmir o _)
    (stageAll o _)

/-- **mulx, total, from any storage that writes slot 0 at every value**. -/
theorem certified_total_at_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Refines fuel c code scopeAtValue :=
  let o : SolarTV.Machine.Oracle := Solar.ethOracle
  Generic.refines_of_defined_stages (source_ends_at_value hc) (loweringAtValue o hc)
    (mirToEvmir o _) (stageAll o _)

/-- The scope has a call (`n(0, 0, 0)` from the deployed storage). -/
theorem scope_inhabited : ∃ call, fullScope fns deployed call :=
  ⟨_, fnN, by simp [fns], [0, 0, 0], rfl, by simp, rfl⟩

end MulX

/-! ### Bank: fuel matters -/

namespace Bank

/-- `balanceOf(0)` from empty storage, the call `scope_inhabited` exhibits. -/
def probeCall : Call :=
  { calldata := calldata fnBalanceOf.sel [0], callvalue := 0, storage := [] }

/-- Whether SolidCore returns nothing on `probeCall` with fuel 2, when the contract checks. -/
def run2? : Option Bool :=
  match contract? with
  | .ok c => some (Source.run 2 c probeCall).isNone
  | .error _ => none

-- `run2_eq`: the kernel's evaluation (the selectors and digests read from their tables, as in
-- `shape_eq`): with fuel 2 SolidCore returns nothing on `probeCall` (with fuel 3 it finishes).
kernel_rfl run2_eq run2? (some true) using selector_eq digest_eq

theorem run2_none {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Source.run 2 c probeCall = none := by
  have h := run2_eq
  unfold run2? at h
  rw [hc] at h
  exact Option.isNone_iff_eq_none.mp (Option.some.inj h)

theorem probeCall_scope : ∃ σ, fullScope fns σ probeCall :=
  ⟨[], fnBalanceOf, by simp [fns], [0], rfl, by simp, rfl⟩

/-- **Negative**: with fuel 2 SolidCore does not end on the scope, so `source_ends` is a claim
about fuel 4096, not one every fuel satisfies. -/
theorem not_source_ends_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Defined (solidCore 2) c (fun call => ∃ σ, fullScope fns σ call) :=
  Generic.not_defined_of_none probeCall_scope (run2_none hc)

/-- **Negative**: and the total refinement at fuel 2 fails, by SolidCore returning nothing on
`probeCall` (a mismatch the kernel evaluates, not a timeout). -/
theorem not_certified_total_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Refines 2 c code (fun call => ∃ σ, fullScope fns σ call) :=
  Generic.not_refines_of_none probeCall_scope (run2_none hc)

end Bank

/-! ### Events: fuel matters -/

namespace Events

/-- `transfer(0, 0)` from empty storage, the call `scope_inhabited` exhibits. -/
def probeCall : Call :=
  { calldata := calldata fnTransfer.sel [0, 0], callvalue := 0, storage := [] }

/-- Whether SolidCore returns nothing on `probeCall` with fuel 2, when the contract checks. -/
def run2? : Option Bool :=
  match contract? with
  | .ok c => some (Source.run 2 c probeCall).isNone
  | .error _ => none

-- `run2_eq`: the kernel's evaluation (the selectors and digests read from their tables, as in
-- `shape_eq`): with fuel 2 SolidCore returns nothing on `probeCall` (with fuel 3 it finishes).
kernel_rfl run2_eq run2? (some true) using selector_eq digest_eq

theorem run2_none {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Source.run 2 c probeCall = none := by
  have h := run2_eq
  unfold run2? at h
  rw [hc] at h
  exact Option.isNone_iff_eq_none.mp (Option.some.inj h)

theorem probeCall_scope : ∃ σ, fullScope fns σ probeCall :=
  ⟨[], fnTransfer, by simp [fns], [0, 0], rfl, by simp, rfl⟩

/-- **Negative**: with fuel 2 SolidCore does not end on the scope, so `source_ends` is a claim
about fuel 4096, not one every fuel satisfies. -/
theorem not_source_ends_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Defined (solidCore 2) c (fun call => ∃ σ, fullScope fns σ call) :=
  Generic.not_defined_of_none probeCall_scope (run2_none hc)

/-- **Negative**: and the total refinement at fuel 2 fails, by SolidCore returning nothing on
`probeCall` (a mismatch the kernel evaluates, not a timeout). -/
theorem not_certified_total_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Refines 2 c code (fun call => ∃ σ, fullScope fns σ call) :=
  Generic.not_refines_of_none probeCall_scope (run2_none hc)

end Events

/-! ### MulX: fuel matters -/

namespace MulX

open SolarTV.Export.Main

/-- `n(0, 0, 0)` from the deployed storage, the call `scope_inhabited` exhibits. -/
def probeCall : Call :=
  { calldata := calldata fnN.sel [0, 0, 0], callvalue := 0, storage := deployed }

/-- Whether SolidCore returns nothing on `probeCall` with fuel 2, when the contract checks. -/
def run2? : Option Bool :=
  match contract? with
  | .ok c => some (Source.run 2 c probeCall).isNone
  | .error _ => none

-- `run2_eq`: the kernel's evaluation (the selectors and digests read from their tables, as in
-- `shape_eq`): with fuel 2 SolidCore returns nothing on `probeCall` (with fuel 3 it finishes).
kernel_rfl run2_eq run2? (some true) using selector_eq

theorem run2_none {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Source.run 2 c probeCall = none := by
  have h := run2_eq
  unfold run2? at h
  rw [hc] at h
  exact Option.isNone_iff_eq_none.mp (Option.some.inj h)

theorem probeCall_scope : fullScope fns deployed probeCall :=
  ⟨fnN, by simp [fns], [0, 0, 0], rfl, by simp, rfl⟩

/-- **Negative**: with fuel 2 SolidCore does not end on the scope, so `source_ends` is a claim
about fuel 4096, not one every fuel satisfies. -/
theorem not_source_ends_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Defined (solidCore 2) c (fullScope fns deployed) :=
  Generic.not_defined_of_none probeCall_scope (run2_none hc)

/-- **Negative**: and the total refinement at fuel 2 fails, by SolidCore returning nothing on
`probeCall` (a mismatch the kernel evaluates, not a timeout). -/
theorem not_certified_total_two {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    ¬ Refines 2 c code (fullScope fns deployed) :=
  Generic.not_refines_of_none probeCall_scope (run2_none hc)

end MulX

/-- info: 'SolidCore.Refinement.Generic.definedAtValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.definedAtValue

/-- info: 'SolidCore.Refinement.Generic.not_refines_of_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Generic.not_refines_of_none

/-- info: 'SolidCore.Refinement.Solar.Bank.source_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bank.source_ends

/-- info: 'SolidCore.Refinement.Solar.Bank.certified_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bank.certified_total

/-- info: 'SolidCore.Refinement.Solar.Bank.certified_total_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bank.certified_total_value

/-- info: 'SolidCore.Refinement.Solar.Events.source_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Events.source_ends

/-- info: 'SolidCore.Refinement.Solar.Events.certified_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Events.certified_total

/-- info: 'SolidCore.Refinement.Solar.Events.certified_total_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Events.certified_total_value

/-- info: 'SolidCore.Refinement.Solar.MulX.source_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.source_ends

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.certified_total

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_total_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.certified_total_at

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_total_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.certified_total_value

/-- info: 'SolidCore.Refinement.Solar.MulX.certified_total_at_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.certified_total_at_value

/-- info: 'SolidCore.Refinement.Solar.Bank.not_source_ends_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bank.not_source_ends_two

/-- info: 'SolidCore.Refinement.Solar.Bank.not_certified_total_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bank.not_certified_total_two

/-- info: 'SolidCore.Refinement.Solar.Events.not_source_ends_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Events.not_source_ends_two

/-- info: 'SolidCore.Refinement.Solar.Events.not_certified_total_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Events.not_certified_total_two

/-- info: 'SolidCore.Refinement.Solar.MulX.not_source_ends_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.not_source_ends_two

/-- info: 'SolidCore.Refinement.Solar.MulX.not_certified_total_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MulX.not_certified_total_two

end SolidCore.Refinement.Solar
