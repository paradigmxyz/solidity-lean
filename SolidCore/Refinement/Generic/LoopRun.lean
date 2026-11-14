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
      some (T.eval ⟨args, slotValue σ, solHash⟩).obs := by
  unfold runtimeRun runtimeResult?
  simp only [Dirty.bytes_calldata]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = Wide.ctxOf c from rfl]
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec]
  have hp := (widthsOf_spec hw).2.2.1
  have hr : ∀ r ∈ fn.returns, RetTy r.ty ∧ r.isStorageRef = false :=
    fun r hr => wordBinding_ty (List.all_eq_true.mp hret r hr)
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress callerAddress 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ State.empty with
      storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) State.empty.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, slotValue σ, solHash⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  set K := argFacts ws 0 with hK
  have hKρ : K.Hold ρ := argFacts_hold ρ hargs ws 0 (by simpa [hρ] using hclean)
  set E : EraseEnv := { envOf c.core with facts := K } with hE
  have hframe : fn.initialFrame? (args.map .word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (args.map .word) =
        some (frameOf ρ (paramLocals fn.params 0)) :=
      bindArgs_words ρ hargs fn.params 0 hp (by simp [hρ, hlen])
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings,
      defaults_words ρ fn.returns hr, frameOf, List.map_append]
  have hrel : StmtRel ρ E ctx
      { state := { st0 with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] }
      (initState fn) :=
    { fields := by subst hctx; rfl
      events := by subst hctx; rfl
      checked := by subst hctx; rfl
      sender := by subst hctx; rfl
      hash := rfl
      ok := hρok
      frames := rfl
      store := by
        intro k hk
        have := getD_storage_empty σ k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) State.empty.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [State.empty, initState]
      facts := hKρ }
  obtain ⟨r, hrun, hleaf⟩ := hb ρ ctx _ hrel
  have hcall : fn.call? fuel c.core.table ctx st0 (args.map .word) =
      some (fn.callBodyResult st0 r) := by
    have hacc' : fn.acceptsValue ctx.value = true := hctxv ▸ hacc
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, hacc', hframe,
      if_true, Option.map_some, Option.bind_some]
    rw [show c.core.table = E.tbl from rfl, hrun]
    rfl
  obtain ⟨T', hT', hTe⟩ := brTree_eval fn K ρ b T hT
  rw [hacc, if_pos rfl, hcall, ← hTe]
  generalize b.eval ρ = l at hT' hleaf
  cases l with
  | normal S =>
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt
    simp only [leafTree, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
    obtain ⟨ws, hws, hT'⟩ := hT'
    split at hT'
    case isFalse => simp at hT'
    rename_i hok
    simp only [Option.some.injEq] at hT'
    subst hT'
    simp only [FunctionDef.callBodyResult, FunctionDef.collectReturns, collectReturnBindings,
      collect_words ρ rt S hKρ hleaf.expr.locals fn.returns ws hok hws, untag_words,
      encode_words ρ hKρ fn.returns ws hok, bind, Option.bind, Option.map_some]
    simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  | returned S vs =>
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt vals
    obtain ⟨hst', rfl⟩ := hleaf
    by_cases hv : vs = []
    · subst hv
      simp only [leafTree, if_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
      obtain ⟨ws, hws, hT'⟩ := hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      simp only [FunctionDef.callBodyResult, List.map_nil, List.isEmpty_nil, if_true,
        FunctionDef.collectReturns, collectReturnBindings,
        collect_words ρ rt S hKρ hst'.expr.locals fn.returns ws hok hws, untag_words,
        encode_words ρ hKρ fn.returns ws hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
        hst'.logs, Option.some.injEq, Observable.mk.injEq, true_and]
      funext slot
      exact loadSlot_eq _ S.writes ρ hρok hst'.store slot
    · simp only [leafTree, hv, if_false] at hT'
      split at hT'
      case isFalse => simp at hT'
      rename_i hok
      simp only [Option.some.injEq] at hT'
      subst hT'
      have hne : (vs.map fun e => Value.word (e.eval ρ)).isEmpty = false := by
        cases vs with
        | nil => exact absurd rfl hv
        | cons _ _ => rfl
      simp only [FunctionDef.callBodyResult, hne, Bool.false_eq_true, if_false,
        FunctionDef.coerceReturnValues, coerceReturnBindings,
        coerce_words ρ rt hKρ fn.returns vs hok, untag_words,
        encode_words ρ hKρ fn.returns vs hok, bind, Option.bind, Option.map_some]
      simp only [Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
        hst'.logs, Option.some.injEq, Observable.mk.injEq, true_and]
      funext slot
      exact loadSlot_eq _ S.writes ρ hρok hst'.store slot
  | reverted p =>
    cases r <;> simp only [LeafRel] at hleaf
    subst hleaf
    cases p with
    | empty =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data,
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ]

/-- info: 'SolidCore.Refinement.Generic.Loop.runtime_run_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runtime_run_clean

end SolidCore.Refinement.Generic.Loop
