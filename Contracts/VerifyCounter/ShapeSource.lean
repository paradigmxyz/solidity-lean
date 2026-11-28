import Contracts.VerifyCounter.Shape
import Contracts.VerifyCounter.StageSource

/-!
# VerifyCounter's bump with a SolidCore source: all four obligations

The source of this statement is SolidCore's checked `Counter` (`Source.contract?`: the type
checker on the solc AST of crates/verify/examples/Counter.sol, checked by the kernel), run by
`solidCoreRuntime fuel` (SolidCore's ABI dispatcher on the runtime code from the call's storage;
deployment and the constructor are outside the statement). The bytes are the exact runtime
bytecode solar emitted (`SolarTV.Milestone.VerifyCounter.code`), run by EthLib at an explicit gas
under `Shapes.oracle` (EthLib's caller, Keccak-256 and environment).

The valid calls `ValidS`: `bump(n)` with ABI call data (selector and one word), no value, from
any storage, with `n < 2 ^ 32` (where the proved gas bound, linear in `n`, stays below
`2 ^ 64`). On them:

* equivalence: every result of the bytecode at every gas below `2 ^ 256` is SolidCore's result,
  or a failure that changes nothing (out of gas among them): the MIR-sourced equivalence
  (`Shape.functional`) with the source stage `Source.mir_eq` (SolidCore and `stage0` give the
  same observable);
* termination: SolidCore's run ends on every valid call (`Source.runs`, the loop by its kernel
  checked ranking certificate `n - i`), with an allowed status: success, `Panic(0x11)` or
  `Error("over")` (`Allowed`), never another revert;
* the specification: solar-verify's `VerifyCounter.spec` (`count == old(count) + n`, the
  `require`) of every SolidCore result (`holds_stage0` carried by `mir_eq`);
* resources: from `Bump.gasBound call` gas on, the bytecode gives exactly SolidCore's result
  (`Shape.resources`, then `mir_eq`).

Trust boundary: SolidCore's semantics of the checked contract, the solc AST import (solc 0.8.35),
and EthLib's EVM. No hypothesis besides the oracle's definition.
-/

namespace Contracts.VerifyCounter.ShapeSource

open SolidCore.Refinement SolarTV Contracts.VerifyCounter.Source SolidCore.Refinement.Generic.Loop

/-- The declared valid calls: `bump(n)` with `n < 2 ^ 32`, no value, any storage. -/
def ValidS (call : Call) : Prop := ∃ σ a, a < 2 ^ 32 ∧ call = bumpCall σ a

/-- The statuses the statement allows: success, or one of bump's two declared reverts. -/
def Allowed (_ : Call) (obs : Observable) : Prop :=
  obs.success = true ∨
    obs.output = SolarTV.Milestone.VerifyCounter.Bump.panicData.map BitVec.toNat ∨
    obs.output = SolarTV.Milestone.VerifyCounter.Bump.overData.map BitVec.toNat

theorem validB {call : Call} (h : ValidS call) : ShapeSpec.ValidB call := by
  obtain ⟨σ, a, ha, rfl⟩ := h
  obtain ⟨hsel, hn⟩ := bumpCall_facts σ a (by omega)
  refine ⟨hsel, ?_⟩
  rw [hn, toNat_ofNat_lt (by omega)]
  exact ha

theorem allowed_of {c : SolidCore.Solidity.TypeCheck.CheckedContract} (hc : contract? = .ok c)
    (σ : List (Nat × Nat)) (a : Nat) (ha : a < 2 ^ 256) {obs : Observable}
    (h : runtimeRun fuel c (bumpCall σ a) = some obs) : Allowed (bumpCall σ a) obs :=
  result_kinds Shapes.oracle hc σ a ha h

/-- **The published statement, from SolidCore's source**: all four obligations on the exact
bytecode. -/
theorem published : ∃ c, contract? = .ok c ∧
    Shapes.Certified (solidCoreRuntime fuel) c SolarTV.Milestone.VerifyCounter.code ValidS Allowed
      (Shapes.specPost SolidCore.Refinement.Solar.VerifyCounter.spec)
      SolarTV.Milestone.VerifyCounter.Bump.gasBound := by
  obtain ⟨c, hc⟩ := contract_ok
  obtain ⟨T, hT⟩ := tree_ok
  refine ⟨c, hc, ⟨⟨bumpCall [] 0, [], 0, by decide, rfl⟩, ?_, ?_, ?_, ?_⟩⟩
  · rintro gas hg _ ⟨σ, a, ha, rfl⟩ obs hrun
    have h := Shape.functional.equiv gas hg _ (validB ⟨σ, a, ha, rfl⟩).1 obs hrun
    rwa [mir_eq Shapes.oracle hc σ a (by omega)] at h
  · rintro _ ⟨σ, a, ha, rfl⟩
    exact ⟨_, runs hc hT σ a (by omega), allowed_of hc σ a (by omega) (runs hc hT σ a (by omega))⟩
  · rintro _ ⟨σ, a, ha, rfl⟩ obs h
    change runtimeRun fuel c (bumpCall σ a) = some obs at h
    rw [← mir_eq Shapes.oracle hc σ a (by omega)] at h
    exact Shape.functional.meets _ (validB ⟨σ, a, ha, rfl⟩).1 obs h
  · rintro _ ⟨σ, a, ha, rfl⟩
    obtain ⟨hlt, hrun⟩ := Shape.resources _ (validB ⟨σ, a, ha, rfl⟩)
    exact ⟨hlt, fun gas h1 h2 => (hrun gas h1 h2).trans (mir_eq Shapes.oracle hc σ a (by omega))⟩

/-- info: 'Contracts.VerifyCounter.ShapeSource.published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms published

end Contracts.VerifyCounter.ShapeSource
