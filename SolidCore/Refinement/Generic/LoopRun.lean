import SolidCore.Refinement.Generic.Loop
import SolidCore.Refinement.Generic.SourceRun

/-!
# SolidCore's runtime code, and calls of functions whose body is not loop-free

Two pieces the generic source stage needs before a function with a loop can join it.

* `solidCoreRuntime fuel`: SolidCore on the runtime code alone. `solidCore` (`Source.run`) first
  runs the constructor **with no arguments**, so a contract whose constructor takes parameters
  (solar-verify's `Counter`, `constructor(uint256 _limit)`) has no run at all there. Here the call
  runs through the same ABI dispatcher (`ABI.Contract.callCalldataAtFromWithContext?`) from the
  state whose storage is the call's, with no constructor: deployment is outside the statement, as
  it is outside every runtime-bytecode statement (`Target.run` runs the runtime code from the
  call's storage too).
* `BodyRuns E fuel fn b`: the body of `fn` runs, from every runtime related to the function's
  first symbolic state, to the leaf of `b` the call's words select. `eval_stmt` gives it of an
  erased (loop-free) body; a loop's ranking certificate (`Loop.lean`) gives it of a body with
  loops. `runtime_run` is `source_run` with that as its only premise about the body: the call shows
  the observable of the tree `brTree` makes of `b`, whatever its argument words.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

/-- SolidCore's result of `call` on the runtime code of `c` alone: the ABI dispatcher from the state
whose storage is the call's. -/
def runtimeResult? (fuel : Nat) (c : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  ABI.Contract.callCalldataAtFromWithContext? fuel c.core
    { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
    { State.empty with
      storage := call.storage.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2)
        State.empty.storage }
    selfAddress callerAddress call.callvalue (call.calldata.data.toList.map (·.toNat))

/-- SolidCore on the runtime code alone, observed as `Source.run` observes. -/
def runtimeRun (fuel : Nat) (c : TypeCheck.CheckedContract) (call : Call) : Option Observable :=
  (runtimeResult? fuel c call).map (Source.observe call)

/-- **SolidCore's runtime code**, with statement fuel `fuel`. -/
def solidCoreRuntime (fuel : Nat) : Sem :=
  { Prog := TypeCheck.CheckedContract, run := runtimeRun fuel }

/-- The body of `fn` runs to the leaf of `b` from every runtime related to its first state. -/
def BodyRuns (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) (b : Br) : Prop :=
  ∀ ρ ctx rt, StmtRel ρ E ctx rt (initState fn) →
    ∃ r, Stmt.eval fuel E.tbl ctx rt fn.body = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ)

/-- An erased body runs as its erasure. -/
theorem bodyRuns_of_erase {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {b : Br}
    (h : eraseStmt E fuel fn.body (initState fn) = some b) : BodyRuns E fuel fn b :=
  fun ρ ctx rt hrel => eval_stmt ρ E ctx fuel fn.body (initState fn) b h rt hrel

theorem getD_storage_empty (σ : List (Nat × Nat)) (k : Nat) :
    ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) State.empty.storage)[k % 2 ^ 256]?).getD 0 =
      slotValue σ k := by
  rw [Verify.getElem?_foldl_insertLoop]
  apply getD_foldl_cover k σ _ 0
  left
  simp [State.empty]

/-! ## A call on clean argument words -/

/-- **A call of a function with clean argument words runs as the tree of its body's leaves.** -/
theorem runtime_run_clean {fuel : Nat} {c : TypeCheck.CheckedContract} {σ : List (Nat × Nat)}
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold runtimeRun runtimeResult?
  simp only [Dirty.bytes_calldata]
  have hwT := widthsOf_T hw
  exact And.right (abi_clean hsel hfind hwT.1 (retBinding_of_word hret) fuel _ callerAddress (getD_storage_empty σ) rfl
    (.lit callerWord) hlen hargs (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)) rfl (tagsOk_of_words (words_of_widths hw hret))
    (by rw [tyVals_params hw hlen]; exact hdec) hT (fun rt hrel => hb _ _ rt hrel) _ rfl)

/-- info: 'SolidCore.Refinement.Generic.Loop.runtime_run_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runtime_run_clean


/-! ## The runtime code from any caller -/

/-- `runtimeResult?` with the call sent by `caller`: the same dispatcher, context and state, with
`caller` as the call's sender. `runtimeResult?` is its default instance
(`runtimeResult?_eq_from`). -/
def runtimeResultFrom? (caller fuel : Nat) (c : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  ABI.Contract.callCalldataAtFromWithContext? fuel c.core
    { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
    { State.empty with
      storage := call.storage.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2)
        State.empty.storage }
    selfAddress caller call.callvalue (call.calldata.data.toList.map (·.toNat))

/-- SolidCore on the runtime code alone from `caller`, observed as `Source.run` observes. -/
def runtimeRunFrom (caller fuel : Nat) (c : TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  (runtimeResultFrom? caller fuel c call).map (Source.observe call)

/-- **SolidCore's runtime code from `caller`**, with statement fuel `fuel`. -/
def solidCoreRuntimeFrom (caller fuel : Nat) : Sem :=
  { Prog := TypeCheck.CheckedContract, run := runtimeRunFrom caller fuel }

theorem runtimeResult?_eq_from (fuel : Nat) :
    runtimeResult? fuel = runtimeResultFrom? callerAddress fuel :=
  rfl

theorem runtimeRun_eq_from (fuel : Nat) : runtimeRun fuel = runtimeRunFrom callerAddress fuel :=
  rfl

theorem solidCoreRuntime_eq_from (fuel : Nat) :
    solidCoreRuntime fuel = solidCoreRuntimeFrom callerAddress fuel :=
  rfl

end SolidCore.Refinement.Generic.Loop
