import SolidCore.Refinement.Behaviours
import SolidCore.Solidity.FuelExtension

/-!
# Fuel never makes a SolidCore result

`Source.run fuel` runs the constructor, then the ABI dispatcher, both with statement fuel `fuel`.
`SolidCore.Solidity.Source.ABI.Contract.callCalldataAtFromWithContext?_fuel_mono`
(`Solidity/FuelExtension.lean`) proves the dispatcher fuel-monotone along every path, so a
dispatched call that gives a result at some fuel gives the same result at every higher fuel:
running out of statement fuel only withholds a result (`none`), never produces one.

`run_fuel_mono` lifts that to `Source.run` for a contract whose constructor gives the same
result at both fuels (`CtorStable`). The constructor runs under a self-dispatch hook whose depth
is the fuel itself (`CheckedContract.constructWithContext?`), so its tree is not literally the same
function of the fuel; the hook is unreachable during construction (a self-call there reverts or
fails closed before reaching it), but that is not proved here, so `CtorStable` stays a hypothesis.

`Refines.fuel_mono` and `Satisfies.fuel_mono` carry the end-to-end statements to every higher
fuel under the same hypothesis: a theorem proved at the fuel the corpus fixes is not an artefact
of that fuel.
-/

namespace SolidCore.Refinement

open SolidCore.Solidity SolidCore.Solidity.Source

/-- The context `Source.result?` runs `contract` in for `call`. -/
def Source.contextOf (contract : TypeCheck.CheckedContract) (call : Call) : Context :=
  { contract.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }

/-- The constructor gives the same result at fuels `n` and `m`. -/
def CtorStable (n m : Nat) (contract : TypeCheck.CheckedContract) (call : Call) : Prop :=
  TypeCheck.CheckedContract.constructWithContext? n contract (Source.contextOf contract call)
      State.empty selfAddress 0 [] =
    TypeCheck.CheckedContract.constructWithContext? m contract (Source.contextOf contract call)
      State.empty selfAddress 0 []

theorem Source.result?_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : TypeCheck.CheckedContract} {call : Call} (hctor : CtorStable n m contract call)
    {r : TypeCheck.CoreAbiCallResult} (h : Source.result? n contract call = some r) :
    Source.result? m contract call = some r := by
  unfold Source.result? at h ⊢
  unfold CtorStable Source.contextOf at hctor
  dsimp only at h hctor ⊢
  rw [← hctor]
  split at h
  next deployed _ hdep =>
    unfold TypeCheck.CheckedContract.callCalldataAtFromWithContext? at h ⊢
    exact ABI.Contract.callCalldataAtFromWithContext?_fuel_mono hnm h
  next => cases h

/-- **A finished SolidCore run is the run at every higher fuel**, for a stable constructor. -/
theorem Source.run_fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : TypeCheck.CheckedContract} {call : Call} (hctor : CtorStable n m contract call)
    {obs : Observable} (h : Source.run n contract call = some obs) :
    Source.run m contract call = some obs := by
  unfold Source.run at h ⊢
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Source.result?_fuel_mono hnm hctor hr]
  rfl

theorem Refines.fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : TypeCheck.CheckedContract} {code : ByteArray} {scope : Call → Prop}
    (hctor : ∀ call, scope call → CtorStable n m contract call)
    (h : Refines n contract code scope) : Refines m contract code scope := by
  intro call hc
  obtain ⟨obs, h1, h2⟩ := h call hc
  exact ⟨obs, Source.run_fuel_mono hnm (hctor call hc) h1, h2⟩

theorem Satisfies.fuel_mono {n m : Nat} (hnm : n ≤ m)
    {contract : TypeCheck.CheckedContract} {scope pre : Call → Prop}
    {post : Call → Observable → Prop}
    (hctor : ∀ call, scope call → CtorStable n m contract call)
    (h : Satisfies (solidCore n) contract scope pre post) :
    Satisfies (solidCore m) contract scope pre post := by
  intro call hc hp
  obtain ⟨obs, h1, h2⟩ := h call hc hp
  exact ⟨obs, Source.run_fuel_mono hnm (hctor call hc) h1, h2⟩

/--
info: 'SolidCore.Refinement.Source.run_fuel_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Source.run_fuel_mono

end SolidCore.Refinement
