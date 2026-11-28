import Contracts.CallFamilies.Core
import Contracts.CallFamilies.FeeOnSource

/-!
# The source stages of `sync` and `feeOn` for `Calls`'s checked core

The hypotheses `sync_stage_in` and `feeOn_stage_in` take of the checked contract (its `sync` and
`feeOn` bodies, its storage fields, an empty account seed, and a constructor that leaves no storage,
logs, transient storage or adopted world) hold of SolidCore's checked `Calls`: the kernel evaluates
the type checker once (`kernel_rfl`, with the selectors from `Core`'s table) and compares the
result with the literals the stages use. `calls_sync_stage` and `calls_feeOn_stage` are the
stages with only the world's hypotheses left: `CallsAgree o V`, seeded code at addresses below
`2 ^ 160`, and return data shorter than `2 ^ 256` bytes.
-/

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation
open SolidCore.Verify.VC.Calls (contract? fuel)

/-- What the constructor of `c` leaves: no storage, no logs, no transient storage, no adopted
world. -/
def deployFacts (c : SolidCore.Solidity.TypeCheck.CheckedContract) : Bool :=
  match SolidCore.Solidity.TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c)
      State.empty selfAddress 0 [] with
  | some (CallResult.returned d _) =>
    d.storage.toList.isEmpty && d.events.isEmpty && d.transient.toList.isEmpty && d.envWorld?.isNone
  | _ => false

theorem deployFacts_of {c : SolidCore.Solidity.TypeCheck.CheckedContract} (h : deployFacts c = true) :
    ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  unfold deployFacts at h
  split at h
  next d vs hc =>
    simp only [Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
    exact ⟨d, ⟨⟨vs, hc⟩, h.1.1.1, h.1.1.2⟩, h.1.2, h.2⟩
  next => simp at h

/-- The facts of the checked `Calls` the stages take. -/
def callsFacts : Option (Option FunctionDef × Option FunctionDef × List StorageField × Bool) :=
  match contract? with
  | .ok c => some (c.core.findFunctionBySelector? 4294363881, c.core.findFunctionBySelector? 1328766218,
      c.core.storageFields,
      c.core.context.accountBalances.isEmpty && c.core.context.accountCodehashes.isEmpty &&
        c.core.context.accountCodes.isEmpty && deployFacts c)
  | .error _ => none

kernel_rfl callsFacts_eq callsFacts (some (some syncFn, some feeOnFn, callsFields, true)) using SolidCore.Verify.VC.Calls.selector_eq SolidCore.Verify.VC.mkIdx_eq

theorem calls_facts : ∃ c, contract? = .ok c ∧
    c.core.findFunctionBySelector? 4294363881 = some syncFn ∧
    c.core.findFunctionBySelector? 1328766218 = some feeOnFn ∧
    c.core.storageFields = callsFields ∧
    c.core.context.accountBalances = [] ∧ c.core.context.accountCodehashes = [] ∧
    c.core.context.accountCodes = [] ∧
    ∃ d, Wide.DeployedAt fuel c d [] ∧ d.transient.toList = [] ∧ d.envWorld? = none := by
  have h := callsFacts_eq
  unfold callsFacts at h
  split at h
  next c hc =>
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨h1, h2, h3, ⟨⟨hb, hh⟩, hcc⟩, hdep⟩ := h
    exact ⟨c, hc, h1, h2, h3, hb, hh, hcc, deployFacts_of hdep⟩
  next => simp at h

/-- **sync's source stage for `Calls`**: SolidCore's checked `Calls` in a world `V` refines solar's
stage0 on `sync()` under every oracle agreeing with `V`, from every storage whose token is not the
contract itself. -/
theorem calls_sync_stage : ∃ c, contract? = .ok c ∧ ∀ (V : World),
    (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
    (∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256) →
    ∀ (o : Machine.Oracle), CallsAgree o V →
    Stage (solidCoreIn V fuel) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, slotValue σ 1 % 2 ^ 160 ≠ selfAddress ∧ call = Sync.syncCall σ) := by
  obtain ⟨c, hc, h1, -, h3, hb, hh, hcc, d, hd, hdt, hde⟩ := calls_facts
  exact ⟨c, hc, fun V hk hs o agree =>
    sync_stage_in 4091 V hd h1 h3 hdt hde hb hh hcc hk hs o agree⟩

/-- **feeOn's source stage for `Calls`**, from every storage whose factory is not the contract
itself. -/
theorem calls_feeOn_stage : ∃ c, contract? = .ok c ∧ ∀ (V : World),
    (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
    (∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 256) →
    ∀ (o : Machine.Oracle), CallsAgree o V →
    Stage (solidCoreIn V fuel) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, slotValue σ 0 % 2 ^ 160 ≠ selfAddress ∧ call = FeeOn.feeOnCall σ) := by
  obtain ⟨c, hc, -, h2, h3, hb, hh, hcc, d, hd, hdt, hde⟩ := calls_facts
  exact ⟨c, hc, fun V hk hs o agree =>
    feeOn_stage_in 4091 V hd h2 h3 hdt hde hb hh hcc hk hs o agree⟩

/-- info: 'SolidCore.Refinement.CallFamilies.calls_sync_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calls_sync_stage

/-- info: 'SolidCore.Refinement.CallFamilies.calls_feeOn_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calls_feeOn_stage

end SolidCore.Refinement.CallFamilies
