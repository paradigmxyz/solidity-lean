import Verify.LoopSource.Equiv.CtorBridge
import Verify.LoopSource.Equiv.LoopFrom

/-!
# The load-level deployed run from any caller

\`deployed_run_entry_from a\`: \`deployed_run_entry\` with the call sent by \`a\`. From a load-level
deployment, a call of a function whose body runs to \`b\` from the symbolic-caller first state
(\`BodyRunsFrom\`) runs to the tree's observable at caller word \`a\`.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

theorem deployed_run_entry_from (a : Nat) {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {store : Nat → Nat}
    (hstore : ∀ k, ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 = store k)
    (hok : ∀ k, store (k % wordSize) % wordSize = store k)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRunsFrom { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Refinement.Source.runFromArgs a fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (fixObs σ (T.eval ⟨args, store, solHash, a⟩).obs) := by
  unfold Refinement.Source.runFromArgs
  obtain ⟨vs0, hcons⟩ := hd.cons
  rw [resultFromArgs?_of_cons hcons]
  simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?, Dirty.bytes_calldata, Option.map]
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
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress a 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, store, solHash, a⟩ with hρ
  have hρok : ρ.Ok := hok
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
        have := hstore k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initFrom, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [hd.events, initFrom, initState]
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
    simp only [fixObs, Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
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
      simp only [fixObs, Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
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
      simp only [fixObs, Source.observe, Tree.eval, Res.obs, if_true, ↓reduceIte, logEntries_map,
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
      simp [fixObs, FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data,
        ABI.Contract.encodeRevertData?, fixObs, Source.observe, Tree.eval, Res.obs, hρ]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        fixObs, Source.observe, Tree.eval, Res.obs, hρ]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        fixObs, Source.observe, Tree.eval, Res.obs, hρ]




end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.deployed_run_entry_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.deployed_run_entry_from
