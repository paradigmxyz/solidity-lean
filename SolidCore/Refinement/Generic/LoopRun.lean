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

/-- **The entry of a call on clean argument words**: from any base context, sender `a` and state
`st0` whose slots hold `slotValue σ` and which has no logs, a function of the fragment starts its
body from a runtime related to its first symbolic state with the caller `cw`, the sender's word,
and the call is the body's run turned into the call's result. -/
theorem call_entry {c : TypeCheck.CheckedContract} {fn : FunctionDef} {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) (fuel : Nat) (base : Source.Context) (a : Nat)
    (bytes : List Nat) {st0 : Source.State} {σ : List (Nat × Nat)}
    (hstore : ∀ k, (st0.storage[k % 2 ^ 256]?).getD 0 = slotValue σ k) (hev : st0.events = [])
    {K : Facts} {args : List Nat} {rc : Nat} (cw : WExpr)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hK : K.Hold ⟨args, slotValue σ, solHash, rc⟩)
    (hcw : SolidCore.Solidity.Shared.norm a = cw.eval ⟨args, slotValue σ, solHash, rc⟩) :
    ∃ rt, StmtRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
        (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes) rt
        { initState fn with caller := cw } ∧
      fn.call fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes)
        st0 (args.map .word) =
        some (fn.callBodyResult st0 <$> Stmt.eval fuel c.core.table
          (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes) rt fn.body) := by
  set ctx := ABI.Contract.callContextAtWithBase c.core base selfAddress a 0 bytes with hctx
  set ρ : Val := ⟨args, slotValue σ, solHash, rc⟩ with hρ
  have hr : ∀ r ∈ fn.returns, RetTy r.ty ∧ r.isStorageRef = false :=
    fun r hr => wordBinding_ty (List.all_eq_true.mp hret r hr)
  have hframe : fn.initialFrame? (args.map .word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (args.map .word) =
        some (frameOf ρ (paramLocals fn.params 0)) :=
      bindArgs_words ρ hargs fn.params 0 (widthsOf_spec hw).2.2.1 (by simp [hρ, hlen])
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings,
      defaults_words ρ fn.returns hr, frameOf, List.map_append]
  have hacc : fn.acceptsValue ctx.value = true := by
    simp [hctx, ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm,
      FunctionDef.acceptsValue, wordEq]
  refine ⟨{ state := { st0 with
              selfBalance := SolidCore.Solidity.Shared.addWord
                (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
              worldMutatedSinceAdoption := true }
            locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] },
    { fields := rfl, events := rfl, checked := rfl, sender := hcw, hash := rfl,
      ok := slotValue_store σ, frames := rfl, facts := hK
      store := fun k _ => by
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ, ← hstore k,
          SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases st0.storage[k % wordSize]? <;> rfl
      logs := by simp [hev, initState] }, ?_⟩
  simp only [FunctionDef.call, FunctionDef.evalBodyEntry, hacc, hframe, if_true, Option.map_some]

/-- **A call on clean argument words shows its body's tree**: from any base context, sender and
state as in `call_entry`, a body that runs from every related runtime to the leaf of `b` the
call's words select makes the call a finished one, and the ABI dispatcher shows the tree `brTree`
makes of `b`. -/
theorem abi_clean {c : TypeCheck.CheckedContract} {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) (fuel : Nat) (base : Source.Context) (a : Nat)
    {st0 : Source.State} {σ : List (Nat × Nat)}
    (hstore : ∀ k, (st0.storage[k % 2 ^ 256]?).getD 0 = slotValue σ k) (hev : st0.events = [])
    {K : Facts} {args : List Nat} {rc : Nat} (cw : WExpr)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hK : K.Hold ⟨args, slotValue σ, solHash, rc⟩)
    (hcw : SolidCore.Solidity.Shared.norm a = cw.eval ⟨args, slotValue σ, solHash, rc⟩)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word))
    {b : Br} {T : Tree} (hT : brTree fn K b = some T)
    (hb : ∀ rt, StmtRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
        (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
          ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) rt
        { initState fn with caller := cw } →
      ∃ r, Stmt.eval fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
          ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) rt fn.body =
          .done (.ok r) ∧
        LeafRel ⟨args, slotValue σ, solHash, rc⟩ { envOf c.core with facts := K }
          (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
            ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) r
          (b.eval ⟨args, slotValue σ, solHash, rc⟩))
    (call : Call) (hcs : call.storage = σ) :
    (∃ R, fn.call fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base selfAddress a 0
        ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0 (args.map .word) =
        some (.done (.ok R))) ∧
      Option.map (Source.observe call) (ABI.Contract.callCalldataAtFromWithContext? fuel c.core base
        st0 selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) =
        some (T.eval ⟨args, slotValue σ, solHash, rc⟩).obs := by
  set ρ : Val := ⟨args, slotValue σ, solHash, rc⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  obtain ⟨rt, hrel, hcall⟩ := call_entry (c := c) hw hret fuel base a
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) hstore hev cw hlen hargs
    hK hcw
  obtain ⟨r, hrun, hleaf⟩ := hb rt hrel
  rw [hrun] at hcall
  refine ⟨⟨_, hcall⟩, ?_⟩
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec]
  have hacc : fn.acceptsValue 0 = true := by simp [FunctionDef.acceptsValue, wordEq]
  have hcall' : fn.call? fuel c.core.table (ABI.Contract.callContextAtWithBase c.core base
      selfAddress a 0 ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0
      (args.map .word) = some (fn.callBodyResult st0 r) := by
    simp only [FunctionDef.call?, hcall]
    rfl
  obtain ⟨T', hT', hTe⟩ := brTree_eval fn K ρ b T hT
  rw [hacc, if_pos rfl, hcall', ← hTe]
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
      collect_words ρ rt S hK hleaf.expr.locals fn.returns ws hok hws, untag_words,
      encode_words ρ hK fn.returns ws hok, bind, Option.bind, Option.map_some]
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
        collect_words ρ rt S hK hst'.expr.locals fn.returns ws hok hws, untag_words,
        encode_words ρ hK fn.returns ws hok, bind, Option.bind, Option.map_some]
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
        coerce_words ρ rt hK fn.returns vs hok, untag_words,
        encode_words ρ hK fn.returns vs hok, bind, Option.bind, Option.map_some]
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
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ, hcs]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ, hcs]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ, hcs]

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
  exact And.right (abi_clean hsel hfind hw hret fuel _ callerAddress (getD_storage_empty σ) rfl
    (.lit callerWord) hlen hargs (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)) rfl hdec hT
    (fun rt hrel => hb _ _ rt hrel) _ rfl)

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
