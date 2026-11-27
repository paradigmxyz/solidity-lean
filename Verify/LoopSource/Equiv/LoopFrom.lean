import SolidCore.Refinement.Generic.StageFrom
import SolidCore.Refinement.Generic.LoopRun

/-!
# Loop runs from any caller

`BodyRunsFrom`: the loop route's `BodyRuns` from the symbolic-caller initial state `initFrom fn`
(`msg.sender` the valuation's caller word, bounded below `2 ^ 160` by `callerFact`), so a body
proved to run to `b` this way runs to `b` for every caller.

`runtime_run_clean_from`: from caller `a`, the runtime code (`runtimeRunFrom a`) runs a valid call
of a function whose body runs to `b` to the observable of `b`'s tree at caller word `a`. It is
`runtime_run_clean` with the caller `a`.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

/-- The body of `fn` runs to the leaf of `b` from every runtime related to its symbolic-caller
first state. -/
def BodyRunsFrom (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) (b : Br) : Prop :=
  ∀ ρ ctx rt, StmtRel ρ E ctx rt (initFrom fn) →
    ∃ r, Stmt.eval fuel E.tbl ctx rt fn.body = .done (.ok r) ∧ LeafRel ρ E ctx r (b.eval ρ)

theorem runtime_run_clean_from (a : Nat) (ha : a < 2 ^ 160) {fuel : Nat} {c : TypeCheck.CheckedContract} {σ : List (Nat × Nat)}
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRunsFrom { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    runtimeRunFrom a fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, a⟩).obs := by
  unfold runtimeRunFrom runtimeResultFrom?
  simp only [Dirty.bytes_calldata]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = Wide.ctxOf c from rfl]
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec]
  have hr : ∀ r ∈ fn.returns, RetTy r.ty ∧ r.isStorageRef = false :=
    fun r hr => wordBinding_ty (List.all_eq_true.mp hret r hr)
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress a 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ State.empty with
      storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) State.empty.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, slotValue σ, solHash, a⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  set K : Facts := argFacts ws 0 with hK
  have hKρ : K.Hold ρ := argFacts_hold ρ hargs ws 0 (by simpa [hρ] using hclean)
  set E : EraseEnv := { envOf c.core with facts := K } with hE
  have hframe : fn.initialFrame? (args.map .word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (args.map .word) =
        some (frameOf ρ (paramLocals fn.params 0)) :=
      bindArgs_clean ρ hargs fn.params fn.paramAbiCleanups ws 0 hw (by simpa [hρ] using hclean)
        (by simp [hρ, hlen])
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings,
      defaults_words ρ fn.returns hr, frameOf, List.map_append]
  have hrel : StmtRel ρ E ctx
      { state := { st0 with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] }
      (initFrom fn) :=
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
        simp only [State.loadSlot, StorageMap.lookup?, initFrom, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) State.empty.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [State.empty, initFrom, initState]
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
  rcases l with S | ⟨S, _ | ⟨v, vs⟩⟩ | p <;> cases r <;> simp only [LeafRel] at hleaf <;>
    try obtain ⟨hleaf, rfl⟩ : _ ∧ _ := hleaf
  -- A normal end and a bare `return` both return the named returns' words.
  iterate 2
    rename_i rt
    simp only [leafTree, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at hT'
    obtain ⟨ws, hws, hT'⟩ := hT'
    split at hT'
    case isFalse => simp at hT'
    rename_i hok
    simp only [Option.some.injEq] at hT'
    subst hT'
    simp only [FunctionDef.callBodyResult, List.map_nil, List.isEmpty_nil, ↓reduceIte,
      FunctionDef.collectReturns, collectReturnBindings,
      collect_words ρ rt S hKρ hleaf.expr.locals fn.returns ws hok hws, untag_words,
      encode_words ρ hKρ fn.returns ws hok, bind, Option.bind, Option.map_some]
    simp only [Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  · rename_i rt
    simp only [leafTree, List.cons_ne_nil, ↓reduceIte] at hT'
    split at hT'
    case isFalse => simp at hT'
    rename_i hok
    simp only [Option.some.injEq] at hT'
    subst hT'
    have hne : ((v :: vs).map fun e => Value.word (e.eval ρ)).isEmpty = false := rfl
    simp only [FunctionDef.callBodyResult, hne, Bool.false_eq_true, ↓reduceIte,
      FunctionDef.coerceReturnValues, coerceReturnBindings,
      coerce_words ρ rt hKρ fn.returns (v :: vs) hok, untag_words,
      encode_words ρ hKρ fn.returns (v :: vs) hok, bind, Option.bind, Option.map_some]
    simp only [Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  · subst hleaf
    rcases p with _ | c | m <;> simp only [leafTree, Option.some.injEq, Option.map_eq_some_iff] at hT'
    · subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data,
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ]
    · subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ]
    · obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ]

end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.runtime_run_clean_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.runtime_run_clean_from
