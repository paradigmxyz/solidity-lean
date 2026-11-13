import Verify.Shapes
import Contracts.Counter.Execution
import Contracts.Counter.ShapeSpec
import SolidCore.Refinement.Solar.AssembleGas
import SolidCore.Refinement.Solar.Counter.Assembly

/-!
# Counter in the certified shape

The four obligations of `Shapes.Certified` for solar's freshly exported runtime bytecode of
`Counter` (`CounterRun.code`, `Certified/counter/gen`) against SolidCore's checked `Counter` at
fuel 4096, on the declared valid calls `cspec.Calls` (`inc(uint256)` and `get()` with clean
arguments, any value below `2 ^ 256`, any storage):

* `equiv`: at every gas below `2 ^ 256`, every result of the bytecode is SolidCore's or a failure
  that changes nothing: the source stage (`loweringEvery`) and solar's backend stages
  (`counter_mir_to_evmir`), under every oracle, composed with the assembly checker's per-run
  theorem (`CounterRun.bytecode_runs`, from `checkC`) by `Shapes.equiv_of_runs`.
* `terminates`: SolidCore ends on every valid call within fuel 4096 (`source_run_every`), with an
  allowed status (`allowed`): success, a call with value (neither function is payable), or
  `inc` overflowing slot 0 with `Panic(0x11)`. No other revert is allowed.
* `meets`: solar-verify's specification (`Final.spec`: `inc(d)` ensures `x == old(x) + d`,
  `get()` returns `x`) of every source result (`Shapes.specPost`).
* resources: from 1,281,806 gas on (`ShapeSpec.gasBound`: the straight-line checker's bound,
  22100 per item plus memory), the bytecode shows exactly the source's result, a revert with its
  data included: the forward assembly stage at every gas from the bound on
  (`Assemble.stage_of_check_gas`) after the same source and backend stages (`resources`).

So `published` states `Shapes.Certified`, all four (`certified`).

Negative controls (each by the kernel's evaluation): the assembly checker rejects the bytecode
with one byte changed (`SSTORE` dropped, a jump target moved, an opcode outside the supported set)
and the binding of `final` to the exported hex fails for any other bytes; the specification with
`x == old(x) + d + 1` is not met (`wrong_spec_not_meets`).
-/

namespace SolidCore.Refinement.Solar.Counter.Shape

open SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Evm.Wide SolidCore.Refinement.Wide SolidCore.Refinement.Evm
open SolidCore.Refinement.Solar.Counter.Final SolidCore.Refinement.Solar.Counter.ShapeSpec
open EthLib.Base

theorem allowed_every (call : Call) (h : cspec.Calls call) : allowed call (expectedEvery call) := by
  obtain ⟨f, hf, args, ht, v, hv, σ, rfl⟩ := h
  by_cases h0 : v = 0
  swap
  · exact Or.inr (Or.inl h0)
  subst h0
  simp only [cspec, SolidCore.Refinement.Solar.Counter.Final.spec, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · obtain ⟨a, ha, rfl⟩ := typed_inc ht
    rw [inc_call a 0 ha]
    have hcall : ({ callOf incSelector [BitVec.ofNat 256 a] with callvalue := 0, storage := σ } : Call) =
        { callOf incSelector [BitVec.ofNat 256 a] with storage := σ } := rfl
    rw [hcall, expectedEvery_inc]
    unfold expectedAt
    split_ifs with hof
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, _, rfl, Nat.not_lt.mp hof⟩)
  · obtain rfl := typed_get ht
    rw [get_call, show ({ callAt getSelector [] σ with callvalue := 0 } : Call) =
      callAt getSelector [] σ from rfl, expectedEvery_get]
    exact Or.inl rfl

/-- Source to final EVM IR, under every oracle, on the valid calls. -/
theorem stage (o : SolarTV.Machine.Oracle) {c : SolidCore.Solidity.TypeCheck.CheckedContract}
    (hc : contract? = .ok c) :
    SolarTV.Stage (solidCore fuel) (SolarTV.evmirSem o) c SolarTV.Export.Counter.evm5 cspec.Calls :=
  ((loweringEvery o hc).trans
    ((SolarTV.Milestone.Counter.counter_mir_to_evmir o).mono fun _ _ => trivial)).mono
    fun _ h => calls_every h

theorem inhabited : ∃ call, cspec.Calls call :=
  ⟨_, ⟨incSpec, by simp [cspec, SolidCore.Refinement.Solar.Counter.Final.spec], [1], .cons (by decide) .nil, 0, by decide, [], rfl⟩⟩

theorem functional {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Functional (solidCore fuel) c CounterRun.code cspec.Calls allowed (Shapes.specPost cspec) where
  inhabited := Shape.inhabited
  equiv := Shapes.equiv_of_runs (sem := SolarTV.evmirSem) (q := fun _ => SolarTV.Export.Counter.evm5)
    (Ok := RunOracle.CertOk CounterRun.cert)
    (fun call h => ⟨_, source_run_every hc call (calls_every h)⟩)
    (fun o _ => stage o hc) (CounterRun.bytecode_runs cspec.Calls)
  terminates := Shapes.terminates_of expectedEvery
    (fun call h => source_run_every hc call (calls_every h)) allowed_every
  meets := Shapes.meets_of_holds (holds_of_every fun call h => source_run_every hc call h)

/-- The straight-line checker accepts the fresh bytecode (the certificate of `Counter.Assembly`). -/
theorem check_fresh :
    Assemble.check SolarTV.Export.Counter.evm5 CounterRun.code SolidCore.Refinement.Solar.Counter.cert =
      true := by
  decide +kernel

theorem gasBound_ok :
    Assemble.gasBound SolarTV.Export.Counter.evm5 SolidCore.Refinement.Solar.Counter.cert ≤ 1281806 := by
  decide

/-- **Resources**: from 1,281,806 gas on, the fresh bytecode shows SolidCore's result on every valid
call, through the source and backend stages and the forward assembly stage at every gas from the
checker's bound on (`Assemble.stage_of_check_gas`). -/
theorem resources {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Resources (solidCore fuel) c CounterRun.code cspec.Calls gasBound :=
  Shapes.resources_of_forward (B := SolarTV.evmirSem SolidCore.Refinement.Solar.W1.oracle)
    (q := SolarTV.Export.Counter.evm5)
    (fun call h => ⟨_, source_run_every hc call (calls_every h)⟩)
    (stage _ hc)
    (fun _ hv => ⟨show (1281806 : Nat) < 2 ^ 64 by decide, fun _ h1 _ obs hrun =>
      Assemble.stage_of_check_gas check_fresh _ (fun h => absurd h (by decide)) cspec.Calls
        (Nat.le_trans gasBound_ok h1) _ hv obs hrun⟩)

/-- **All four obligations.** -/
theorem certified {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    Shapes.Certified (solidCore fuel) c CounterRun.code cspec.Calls allowed (Shapes.specPost cspec)
      gasBound :=
  let f := functional hc
  ⟨f.inhabited, f.equiv, f.terminates, f.meets, resources hc⟩

/-- What the published statement asks of this module. -/
theorem published : ∃ c, contract? = .ok c ∧
    Shapes.Certified (solidCore fuel) c CounterRun.code cspec.Calls allowed (Shapes.specPost cspec)
      gasBound := by
  obtain ⟨c, hc⟩ := contract_ok
  exact ⟨c, hc, certified hc⟩

/-- info: 'SolidCore.Refinement.Solar.Counter.Shape.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms certified

/-- info: 'SolidCore.Refinement.Solar.Counter.Shape.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms functional

end SolidCore.Refinement.Solar.Counter.Shape
