import SolidCore.Refinement.Evm.WideStorage
import SolidCore.Refinement.Deploy

/-!
# Deployment from a frame specification

The bytecode half of the lifecycle statement, `Deploys initcode code s`, by a cut point at the
creation frame rather than by reducing EthLib's `processMessage`: `deploys_of_postS` turns a
specification of the one frame a creation runs (from pc 0, with the empty stack and memory, from
the state `Target.preState` gives the creation call) into `Deploys`, for every init code, runtime
code and storage. The frame specification is a Hoare triple of EthLib's program logic, which a
proof states instruction by instruction (`evm_step` and the rules of `Evm.Logic`,
`Evm.WideStorage`), as the runtime stage proofs and Counter's `Deploy.frame` do.

`deployed code s` is what a successful creation shows: the runtime bytes `code`, no logs, and
the storage `slotValue s`.
-/

open EthLib.Base EthLib.Execution EthLib.Execution.Evm EthLib.Execution.Evm.Logic GasCosts
open EthLib.Execution.State
open SolidCore.Refinement SolidCore.Refinement.Evm.Logic SolidCore.Refinement.Evm.Symex
open SolidCore.Refinement.Evm.Wide

namespace Verify.Lifecycle

/-- What a creation that returns `code` and leaves `s` shows. -/
def deployed (code : ByteArray) (s : List (Nat × Nat)) : Observable :=
  { success := true, output := code.data.toList.map (·.toNat), logs := [],
    storage := SolarTV.slotValue s }

/-- **Deployment from the creation frame.** If the frame of every creation message (no value,
no call data, not static, at the contract's address) from the creation call's state stops as
`deployed code s` says, EthLib's run of `initcode` deploys `code` with the storage `s`. -/
theorem deploys_of_postS (initcode code : ByteArray) (s : List (Nat × Nat))
    (h : ∀ msg : Message .fusaka, msg.value = 0 → msg.data = .empty → msg.isStatic = false →
      msg.currentTarget = Target.address selfAddress →
      Spec .fusaka (At initcode msg 0 [] .empty 10000000 (Target.preState initcode deployCall)
        Substate.empty .empty) (PostS (deployed code s) Substate.empty)) :
    Deploys initcode code s := by
  obtain ⟨evm, hr, herr, hout, hst⟩ := processMessage_postS (Target.message initcode deployCall)
    rfl rfl (precompileAddress_message initcode deployCall) (deployed code s)
    (Target.preState initcode deployCall) Substate.empty (h _ rfl rfl rfl rfl)
  have hsucc : evm.1.error.isNone = true := by rw [herr]; rfl
  refine ⟨_, by show Target.run initcode deployCall = _; simp only [Target.run, hr]; rfl, ?_, ?_, ?_⟩
  · exact hsucc
  · exact hout
  · intro k
    simp only [hsucc, ↓reduceIte]
    exact (hst rfl).2 k

end Verify.Lifecycle
