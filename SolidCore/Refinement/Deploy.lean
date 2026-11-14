import SolidCore.Refinement.Compose

/-!
# Deployment

\`Deploys initcode code storage\`: EthLib runs the init code \`initcode\` as a creation does (one frame
with no value and no call data, from the empty storage, the code at the contract's address being
the init code) to success, and the frame returns exactly the runtime bytecode \`code\` and leaves the
storage \`storage\` (\`SolarTV.slotValue\`: the last write of each slot, unwritten slots 0). It is the
fact a deployment theorem proves of solar's init code (\`Counter.deploys\`, Contracts/Counter/Deploys.lean),
and what ties the bytecode a headline is about to the contract that a creation installs.

Not covered, as in Contracts/Counter/Deploy.lean: the creation message's address derivation and the
code deposit (EIP-3541's \`0xef\` check and the 24576-byte limit), which \`deposit_ok\` checks of the
runtime bytecode separately.
-/

namespace SolidCore.Refinement

/-- The creation frame: no call data, no value, the empty storage. -/
def deployCall : Call := { calldata := .empty, callvalue := 0, storage := [] }

/-- EthLib runs \`initcode\` in the creation frame to success, returning \`code\` and leaving
\`storage\`. -/
def Deploys (initcode code : ByteArray) (storage : List (Nat × Nat)) : Prop :=
  ∃ o, ethLib.run initcode deployCall = some o ∧ o.success = true ∧
    o.output = code.data.toList.map (·.toNat) ∧ ∀ k, o.storage k = SolarTV.slotValue storage k

/-- A run of the init code that returns the runtime bytecode and writes no storage deploys it with
the empty storage. -/
theorem deploys_of_run {initcode code : ByteArray} {o : Observable}
    (h : Target.run initcode deployCall = some o) (hs : o.success = true)
    (ho : o.output = code.data.toList.map (·.toNat)) (hst : ∀ k, o.storage k = 0) :
    Deploys initcode code [] :=
  ⟨o, h, hs, ho, fun k => by rw [hst k]; rfl⟩

end SolidCore.Refinement
