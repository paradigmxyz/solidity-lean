import SolidCore.Refinement.Generic.StageFrom

/-!
# A value sent to a non-payable function

`runFromArgs_value_inert`: against a contract deployed with any argument words, a call that selects
a function that is not payable and sends a nonzero value is refused by SolidCore's dispatcher,
whatever the caller, the calldata after the selector and the call storage: the run, if any, fails
with no logs and leaves the call's storage (the three conjuncts of `Verify.Shapes.Inert`). It
reverts before the body runs: on decoded arguments by the value check
(`Contract.rejectedValueCall?`), and on arguments that do not decode by the decode revert.
`resultFromArgs?_value_rejected` names the result on decoded arguments.

A leaf beside `StageFrom`: nothing imports it at its commit, and it changes no definition there, so
`resultFromArgs?_nil` and the other `rfl` lemmas stand.
-/

namespace SolidCore.Refinement.Generic

open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement

/-- The calldata bytes the dispatcher reads. -/
def callBytes (call : Call) : List Nat := call.calldata.data.toList.map (·.toNat)

/-- The deployed state with the call's storage written over it, as `resultFromArgs?` runs it. -/
def overlay (d : Source.State) (call : Call) : Source.State :=
  { d with storage := call.storage.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }

/-- A function that is not payable refuses a nonzero value. -/
theorem acceptsValue_false {f : FunctionDef} {v : Nat} (hpay : f.payable = false)
    (hv : SolidCore.Solidity.Shared.norm v ≠ 0) : f.acceptsValue v = false := by
  simp [FunctionDef.acceptsValue, hpay, wordEq, SolidCore.Solidity.Shared.norm]
  simpa [SolidCore.Solidity.Shared.norm] using hv

/-- **On decoded arguments the value check rejects the call** with an empty revert. -/
theorem resultFromArgs?_value_rejected {caller fuel : Nat} {ws : List Nat}
    {c : TypeCheck.CheckedContract} {call : Call} {d : Source.State} {vs : List Value}
    {sel : Nat} {f : FunctionDef} {args : List Value}
    (hd : Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs))
    (hsel : ABI.readSelector? (callBytes call) = some sel)
    (hf : c.core.findFunctionBySelector? sel = some f)
    (hargs : ABI.decodeFunctionArgs? f ((callBytes call).drop ABI.selectorBytes) = .ok args)
    (hpay : f.payable = false)
    (hv : SolidCore.Solidity.Shared.norm call.callvalue ≠ 0) :
    Refinement.Source.resultFromArgs? caller fuel ws c call =
      some { success := false, output := [], state := overlay d call } := by
  have hacc := acceptsValue_false hpay hv
  simp only [Refinement.Source.resultFromArgs?, hd,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?]
  rw [show (call.calldata.data.toList.map (·.toNat)) = callBytes call from rfl, hsel]
  simp only [hf, hargs, hacc, Bool.false_eq_true, ite_false]
  rfl

/-- **A nonzero value sent to a non-payable function leaves the call inert**: whatever the
caller, the argument bytes and the call storage, the run fails with no logs and the call's own
storage. -/
theorem runFromArgs_value_inert {caller fuel : Nat} {ws : List Nat}
    {c : TypeCheck.CheckedContract} {call : Call} {sel : Nat} {f : FunctionDef}
    (hsel : ABI.readSelector? (callBytes call) = some sel)
    (hf : c.core.findFunctionBySelector? sel = some f)
    (hpay : f.payable = false)
    (hv : SolidCore.Solidity.Shared.norm call.callvalue ≠ 0)
    {obs : Observable} (hrun : Refinement.Source.runFromArgs caller fuel ws c call = some obs) :
    obs.success = false ∧ obs.logs = [] ∧ obs.storage = slotValue call.storage := by
  have hacc := acceptsValue_false hpay hv
  unfold Refinement.Source.runFromArgs Refinement.Source.resultFromArgs? at hrun
  split at hrun
  next d vs hd =>
    simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
      ABI.Contract.callCalldataAtFromWithContext?] at hrun
    rw [show (call.calldata.data.toList.map (·.toNat)) = callBytes call from rfl, hsel] at hrun
    simp only [hf] at hrun
    have key : ∀ r : ABI.AbiCallResult, Option.map (Refinement.Source.observe call) (some r) = some obs →
        r.success = false → obs.success = false ∧ obs.logs = [] ∧ obs.storage = slotValue call.storage := by
      intro r h hs
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [Refinement.Source.observe, hs]
    split at hrun
    next args hargs =>
      simp only [hacc, Bool.false_eq_true, ite_false] at hrun
      exact key _ hrun rfl
    next rv hargs =>
      cases he : ABI.Contract.encodeRevertData? c.core rv with
      | none =>
        simp [ABI.Contract.revertedCall?, he, bind, Option.bind] at hrun
      | some out =>
        simp only [ABI.Contract.revertedCall?, he, bind, Option.bind] at hrun
        exact key _ hrun rfl
  next => simp at hrun

end SolidCore.Refinement.Generic
