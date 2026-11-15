import Contracts.CallFamilies.SourceFacts
import Contracts.CallFamilies.SkimSource

/-!
# skim's source stage for Calls's checked core

The hypotheses skim_stage_in takes of the checked contract hold of SolidCore's checked Calls: one
kernel_rfl of the type checker gives skim's body and pay's table entry (skimFn, payFn), the rest
comes from calls_facts. calls_skim_stage is the stage with only the world's hypotheses left:
CallsAgree o V, seeded code at addresses below 2 ^ 160, return data shorter than 2 ^ 64 bytes.
-/

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolidCore.Refinement SolidCore.Refinement.Generic SolidCore.Refinement.CallNode
open SolidCore.Solidity.Source EvmCompiler.Simulation
open SolidCore.Verify.VC.Calls (contract? fuel)

/-- skim's and pay's entries in the checked Calls. -/
def skimFacts : Option (Option FunctionDef × Option InternalFunction) :=
  match contract? with
  | .ok c => some (c.core.findFunctionBySelector? 3156594551, c.core.table.lookup? payName)
  | .error _ => none

kernel_rfl skimFacts_eq skimFacts (some (some skimFn, some payFn)) using SolidCore.Verify.VC.Calls.selector_eq SolidCore.Verify.VC.mkIdx_eq

/-- **skim's source stage for Calls**: SolidCore's checked Calls in a world V refines solar's stage0
on skim(dst) under every oracle agreeing with V, for every recipient below 2 ^ 160 and every storage
whose token is not the contract itself. -/
theorem calls_skim_stage : ∃ c, contract? = .ok c ∧ ∀ (V : World),
    (∀ p ∈ V.codes.getD [], p.1 < 2 ^ 160) →
    (∀ h world request a, V.ans h (.external world (.call request)) = some a →
      a.returnData.size < 2 ^ 64) →
    ∀ (o : Machine.Oracle), CallsAgree o V →
    Stage (solidCoreIn V fuel) (MIR.Lowered.moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ dst, (dst < 2 ^ 160 ∧ slotValue σ 1 % 2 ^ 160 ≠ selfAddress) ∧
        call = Skim.skimCall σ dst) := by
  obtain ⟨c, hc, -, -, h3, hb, hh, hcc, d, hd, hdt, hde⟩ := calls_facts
  have h := skimFacts_eq
  unfold skimFacts at h
  rw [hc] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨c, hc, fun V hk hs o agree =>
    skim_stage_in 4088 V hd h.1 h.2 h3 hdt hde hb hh hcc hk hs o agree⟩

/-- info: 'SolidCore.Refinement.CallFamilies.calls_skim_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calls_skim_stage

end SolidCore.Refinement.CallFamilies
