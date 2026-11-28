import Contracts.CallFamilies.SyncAgree
import Contracts.CallFamilies.FeeOnAgree

/-!
# The source stages of `sync` and `feeOn` from their source halves

`sync_stage` and `feeOn_stage` compose the MIR halves (`mir_sync_agree`, `mir_feeOn_agree`) with
the source half each function still needs, stated as a proposition of SolidCore alone
(`SyncSource`, `FeeOnSource`): a run of the function in the world `V` that shows `obs` asked `V`
the call the MIR makes, from the world the MIR sees, and shows what the MIR shows for `V`'s answer.
Given it for an open world `V`, every oracle that agrees with `V` (`CallsAgree o V`) runs solar's
stage0 as SolidCore runs the function in `V`: the source stage of a call-making function. The
source halves are not proved here; they are the generic call node's statement-level obligation
(`eraseStmt` of `tryExternalCall` under `foldAns`).
-/

namespace SolidCore.Refinement.CallFamilies

open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Refinement

/-- The source half of `sync`'s stage in the world `V` from the storage `σ`. -/
def SyncSource (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (σ : List (Nat × Nat)) : Prop :=
  ∀ obs, Source.runIn V fuel c (Sync.syncCall σ) = some obs →
    ∃ world request a, Sync.SyncAsk σ V world request a ∧ obs = Sync.obsOf σ a

/-- The source half of `feeOn`'s stage in the world `V` from the storage `σ`. -/
def FeeOnSource (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (σ : List (Nat × Nat)) : Prop :=
  ∀ obs, Source.runIn V fuel c (FeeOn.feeOnCall σ) = some obs →
    ∃ world request a, FeeOn.FeeOnAsk σ V world request a ∧ obs = FeeOn.obsOf σ a

/-- **sync's source stage from its source half**, under every oracle that agrees with `V`. -/
theorem sync_stage (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (scope : List (Nat × Nat) → Prop) (src : ∀ σ, scope σ → SyncSource fuel c V σ)
    (o : Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V fuel) (moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, scope σ ∧ call = Sync.syncCall σ) := by
  rintro call ⟨σ, hσ, rfl⟩ obs hrun
  obtain ⟨world, request, a, hs, rfl⟩ := src σ hσ obs hrun
  exact Sync.mir_sync_agree o V σ world request a agree hs

/-- **feeOn's source stage from its source half**, under every oracle that agrees with `V`. -/
theorem feeOn_stage (fuel : Nat) (c : SolidCore.Solidity.TypeCheck.CheckedContract) (V : World)
    (scope : List (Nat × Nat) → Prop) (src : ∀ σ, scope σ → FeeOnSource fuel c V σ)
    (o : Oracle) (agree : CallsAgree o V) :
    Stage (solidCoreIn V fuel) (moduleSem o) c SolarTV.Export.Calls.stage0
      (fun call => ∃ σ, scope σ ∧ call = FeeOn.feeOnCall σ) := by
  rintro call ⟨σ, hσ, rfl⟩ obs hrun
  obtain ⟨world, request, a, hs, rfl⟩ := src σ hσ obs hrun
  exact FeeOn.mir_feeOn_agree o V σ world request a agree hs

/-- info: 'SolidCore.Refinement.CallFamilies.sync_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sync_stage

/-- info: 'SolidCore.Refinement.CallFamilies.feeOn_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feeOn_stage

end SolidCore.Refinement.CallFamilies
