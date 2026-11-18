import SolidCore.Refinement.Generic.Statement
import SolidCore.Refinement.Generic.LoopRun
import Verify.LoopSource.Generic.Statement
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# From the runtime code to the deployed source: the constructor-argument bridge

\`Source.semAt\` (\`Verify/Generic/Expected.lean\`) runs a call against the contract SolidCore's
constructor leaves on the source's argument words (\`solidCoreFromArgs\`); \`loop_equiv\` gives
\`Shapes.Equiv\` over the runtime code alone (\`solidCoreRuntime\`). This module relates them, exactly:

* **Entry state.** Under the lifecycle statement (\`DeployedAtWith\`, from \`run_of_statement\`'s
  premises), the source's run of a call is the ABI dispatcher on the constructor's state \`d\` with
  the call's storage written over \`d.storage\` (\`resultFromArgs?_of_deployedAtWith\`); the runtime
  code's is the same dispatcher, context and caller on the empty state with the call's storage.
* **Storage, collisions, precedence.** \`getD_deployed_cover\`: every slot of that entry state reads
  \`slotValue σ\` (the call's storage, the last write of a key winning, keys mod \`2 ^ 256\`) when
  every key the constructor wrote is written by the call (\`Covers s σ\`). Without it a slot the
  call does not write reads the constructor's value on the source side and 0 on the runtime side,
  and the two runs can differ, so \`Covers\` is the bridge's premise on the call.
* **Other state fields.** None is assumed: a body's run (\`BodyRuns\`) holds from every runtime its
  relation (\`StmtRel\`) admits, whatever the constructor left in transient storage or immutables;
  its logs are \`d.events\`, which the lifecycle statement makes \`[]\`.
* **Constructor failure.** A constructor that does not return leaves no run
  (\`runFromArgs_eq_none\`), so no Equiv over \`semAt\` holds of a reverting deployment unless every
  bytecode result is inert.

\`deployed_run_clean\` is \`runtime_run_clean\` from the deployed state. \`semAt_eq_runtime\` makes the
two runs equal on a call of a loop-carrying function, and \`equivAt_of_runtime\` turns the runtime
code's \`Shapes.Equiv\` into \`EquivAt (src.semAt Context.default)\` on the valid calls whose storage
covers the deployment.

**Fixed-context evidence only.** The caller is \`callerAddress\` (\`Context.default\`): the loop route's
\`BodyRuns\` is stated for the initial state whose \`msg.sender\` is the constant \`callerWord\`
(\`initState\`), and \`loop_equiv\`'s chain runs the bytes from \`callerAddress\`. Every other caller and
every call value stay OPEN. Counter stays outside the accepted subset.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

/-- **Every slot of the deployed entry state reads the call's storage**, when the call writes every
key the constructor wrote. -/
theorem getD_deployed_cover {fuel : Nat} {args : List TypeCheck.CoreValue} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c args d s)
    {σ : List (Nat × Nat)} (hcov : Covers s σ) (k : Nat) :
    ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 =
      slotValue σ k := by
  rw [Verify.getElem?_foldl_insertLoop]
  apply getD_foldl_cover k σ _ 0
  cases h : d.storage[k % 2 ^ 256]? with
  | none => exact Or.inl rfl
  | some v =>
    right
    have hm : (k % 2 ^ 256, v) ∈ s := hd.storage ▸ Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
    obtain ⟨kv', hkv', he⟩ := hcov _ hm
    exact ⟨kv', hkv', by rw [he]; exact Nat.mod_mod _ _⟩

theorem deployed_run_clean {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws0) d s)
    {σ : List (Nat × Nat)} (hcov : Covers s σ)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Refinement.Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold Refinement.Source.runFromArgs
  rw [resultFromArgs?_of_deployedAtWith hd]
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
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress callerAddress 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, slotValue σ, solHash, callerWord⟩ with hρ
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
        have := getD_deployed_cover hd hcov k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [hd.events, initState]
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


/-! ## Load-level deployment (fixed context; NOT \`DeployedAtWith\`)

\`LoadDeployed\`: SolidCore's constructor on the words returns a state \`d\`, with no logs. It says
nothing of \`d.storage\`'s entry list; facts about \`d\`'s storage are stated through its loads.
\`loadDeployed_of\`: the lifecycle statement's \`DeployedAtWith\` gives it, with every load the value
\`s\` gives at the slot, so this route is strictly more general than the exact one. -/

/-- The constructor on \`ws\` returns \`d\`, with no logs. -/
structure LoadDeployed (fuel : Nat) (c : TypeCheck.CheckedContract) (ws : List Nat) (d : Source.State) : Prop where
  cons : ∃ vs, Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs)
  events : d.events = []

/-- The value the entry list \`s\` gives at slot \`q\`: its first entry's, else 0. -/
def sAt (s : List (Nat × Nat)) (q : Nat) : Nat := ((s.find? (fun kv => kv.1 == q)).map (·.2)).getD 0

/-- **The load cover**: the call writes every slot \`d\` leaves nonzero. -/
def CoversLoad (d : Source.State) (σ : List (Nat × Nat)) : Prop :=
  ∀ k, d.loadSlot k ≠ 0 → ∃ kv ∈ σ, kv.1 % wordSize = k % wordSize

theorem loadSlot_eq_getD (d : Source.State) (k : Nat) :
    d.loadSlot k = (d.storage[k % 2 ^ 256]?).getD 0 := by
  simp only [State.loadSlot, StorageMap.lookup?, SolidCore.Solidity.Shared.norm, modulus_eq,
    Std.HashMap.get?_eq_getElem?]
  generalize d.storage[k % 2 ^ 256]? = o
  cases o <;> rfl

/-- **The exact route gives the load-level one**: \`DeployedAtWith\` gives \`LoadDeployed\`, every load
the value \`s\` gives at the slot mod \`2 ^ 256\`, and \`Covers s\` the load cover. -/
theorem loadDeployed_of {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s) :
    LoadDeployed fuel c ws d ∧ (∀ k, d.loadSlot k = sAt s (k % 2 ^ 256)) ∧
      ∀ σ, Covers s σ → CoversLoad d σ := by
  refine ⟨⟨hd.cons, hd.events⟩, fun k => ?_, fun σ hcov k hk => ?_⟩
  · rw [loadSlot_eq_getD, sAt, ← hd.storage]
    generalize k % 2 ^ 256 = q
    cases h : d.storage[q]? with
    | some v =>
      have hmem : q ∈ d.storage := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [h])
      have := (Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some (m := d.storage)
        (k := q) (k' := q) (v := v)).mpr ⟨Std.HashMap.getKey?_eq_some_of_contains
          (Std.HashMap.contains_iff_mem.mpr hmem), h⟩
      rw [this]; rfl
    | none =>
      have hc : d.storage.contains q = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
      rw [(Std.HashMap.find?_toList_eq_none_iff_contains_eq_false (m := d.storage) (k := q)).mpr hc]; rfl
  · rw [loadSlot_eq_getD] at hk
    generalize hq : k % 2 ^ 256 = q at hk
    cases h : d.storage[q]? with
    | none => simp [h] at hk
    | some v =>
      have hm : (q, v) ∈ s := hd.storage ▸ Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
      obtain ⟨kv', hkv', he⟩ := hcov _ hm
      exact ⟨kv', hkv', by rw [he, ← hq]; exact Nat.mod_mod _ _⟩

theorem resultFromArgs?_of_cons {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {vs : List TypeCheck.CoreValue}
    (h : Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs)) (caller : Nat) (call : Call) :
    Refinement.Source.resultFromArgs? caller fuel ws c call =
      TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel c
        { c.core.context with sender := callerAddress, self := selfAddress, value := call.callvalue }
        { d with
          storage := call.storage.foldl
            (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
        selfAddress caller call.callvalue (call.calldata.data.toList.map (·.toNat)) := by
  simp only [Refinement.Source.resultFromArgs?, h]

/-- What a run shows on \`σ\`: a failure leaves the call's own storage (\`Source.observe\`). -/
def fixObs (σ : List (Nat × Nat)) (o : SolarTV.Observable) : SolarTV.Observable :=
  if o.success then o else { o with storage := slotValue σ }

/-- A tree's failing result keeps the valuation's storage. -/
theorem eval_store_of_fail (ρ : Val) : ∀ T : Tree, (T.eval ρ).success = false → (T.eval ρ).store = ρ.store
  | .halt ok _ _ _, h => by simp only [Tree.eval] at h ⊢; simp [h]
  | .ite c t e, h => by
    simp only [Tree.eval] at h ⊢
    split <;> rename_i hc <;> simp only [hc, ↓reduceIte] at h
    · exact eval_store_of_fail ρ e h
    · exact eval_store_of_fail ρ t h

theorem fixObs_slotValue (σ : List (Nat × Nat)) (args : List Nat) (T : Tree) :
    fixObs σ (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs = (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold fixObs
  split
  · rfl
  · rename_i h
    simp only [Res.obs, Bool.not_eq_true] at h ⊢
    rw [eval_store_of_fail _ T h]

/-- **From a load-level deployment**, a call of a loop-carrying function runs to the tree's
observable at the entry storage's loads \`store\`, whatever the call writes (\`deployed_run_entry\`). -/
theorem deployed_run_entry {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {store : Nat → Nat}
    (hstore : ∀ k, ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 = store k)
    (hok : ∀ k, store (k % wordSize) % wordSize = store k)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Refinement.Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (fixObs σ (T.eval ⟨args, store, solHash, callerWord⟩).obs) := by
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
  generalize hctx : ABI.Contract.callContextAtWithBase c.core (Wide.ctxOf c) selfAddress callerAddress 0
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) = ctx
  generalize hst : ({ d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage } :
    Source.State) = st0
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  have hctxv : ctx.value = 0 := by
    subst hctx; simp [ABI.Contract.callContextAtWithBase, SolidCore.Solidity.Shared.norm]
  set ρ : Val := ⟨args, store, solHash, callerWord⟩ with hρ
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
        have := hstore k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [hd.events, initState]
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



/-- Every slot of the load-deployed entry state reads the call's storage under the load cover. -/
theorem getD_load_cover {d : Source.State} {σ : List (Nat × Nat)} (hcov : CoversLoad d σ) (k : Nat) :
    ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 =
      slotValue σ k := by
  rw [Verify.getElem?_foldl_insertLoop]
  apply getD_foldl_cover k σ _ 0
  by_cases h0 : d.loadSlot k = 0
  · left; rw [loadSlot_eq_getD] at h0; exact h0
  · right; exact hcov k h0

/-- The valid calls of a function that write every slot the load-level deployment left nonzero. -/
def SelCallLoad (sel : Nat) (fn : FunctionDef) (ws : List Nat) (d : Source.State) (call : Call) : Prop :=
  Verify.LoopSource.Generic.SelCall sel fn ws call ∧ CoversLoad d call.storage

/-- **Load-level \`semAt_eq_runtime\`** (fixed context; NOT \`DeployedAtWith\`). -/
theorem semAt_eq_runtime_load {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} (hd : LoadDeployed fuel c ws0 d)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {b : Br} (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) {call : Call}
    (hv : SelCallLoad sel fn ws d call) :
    (solidCoreFromArgs callerAddress fuel ws0).run c call = (solidCoreRuntime fuel).run c call := by
  obtain ⟨⟨σ, args, ⟨hlen, hargs, hclean⟩, rfl⟩, hcov⟩ := hv
  change CoversLoad d σ at hcov
  have hdec := decode_args hw args hlen hargs
  rw [if_pos hclean] at hdec
  show Refinement.Source.runFromArgs callerAddress fuel ws0 c
      { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }
  rw [deployed_run_entry hd (getD_load_cover hcov) (slotValue_store σ) hsel hfind hw hret hb hT args hlen
      hargs hclean hdec, fixObs_slotValue,
    runtime_run_clean hsel hfind hw hret hb hT args hlen hargs hclean hdec]

/-! ## The bridge -/

/-- The valid calls of a function that write every key the deployment wrote. -/
def SelCallCov (sel : Nat) (fn : FunctionDef) (ws : List Nat) (s : List (Nat × Nat)) (call : Call) : Prop :=
  Verify.LoopSource.Generic.SelCall sel fn ws call ∧ Covers s call.storage

/-- **On a covering call of a loop-carrying function, the source deployed with \`ws0\` and the
runtime code run alike**, both to the function's tree. -/
theorem semAt_eq_runtime {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws0) d s)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {b : Br} (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) {call : Call}
    (hv : SelCallCov sel fn ws s call) :
    (solidCoreFromArgs callerAddress fuel ws0).run c call = (solidCoreRuntime fuel).run c call := by
  obtain ⟨⟨σ, args, ⟨hlen, hargs, hclean⟩, rfl⟩, hcov⟩ := hv
  change Covers s σ at hcov
  have hdec := decode_args hw args hlen hargs
  rw [if_pos hclean] at hdec
  show Refinement.Source.runFromArgs callerAddress fuel ws0 c
      { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ }
  rw [deployed_run_clean hd hcov hsel hfind hw hret hb hT args hlen hargs hclean hdec,
    runtime_run_clean hsel hfind hw hret hb hT args hlen hargs hclean hdec]

/-- **The runtime code's equivalence is the deployed source's**, in \`Context.default\`, on the valid
calls whose storage covers the deployment. Fixed-context evidence: every other caller stays OPEN. -/
theorem equivAt_of_runtime {ws0 : List Nat} {src : SolidCore.Verify.Generic.Source ws0}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : Verify.Lifecycle.DeployedAtWith src.fuel c (Verify.Lifecycle.wordArgs ws0) d s)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {b : Br} (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } src.fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) {code : ByteArray}
    (heq : Shapes.Equiv (solidCoreRuntime src.fuel) c code (Verify.LoopSource.Generic.SelCall sel fn ws)) :
    SolidCore.Verify.Generic.EquivAt (src.semAt SolidCore.Verify.Generic.Context.default) c
      SolidCore.Verify.Generic.Context.default code (SelCallCov sel fn ws s) := by
  intro gas hg call hv obs hrun
  have hrun' : Final.Target.runWith gas code call = some obs := by
    rw [← Final.Target.runWithFrom_callerAddress]; exact hrun
  have h := heq gas hg call hv.1 obs hrun'
  rcases h with h | h
  · left
    show (solidCoreFromArgs callerAddress src.fuel ws0).run c call = some obs
    rw [semAt_eq_runtime hd hsel hfind hw hret hb hT hv]; exact h
  · right; exact h

/-- **From the lifecycle statement**: the same, with the deployment named by \`run_of_statement\`'s
premises (\`hb\`: the creation code carries the source's words; \`hl\`: the lifecycle statement). -/
theorem equivAt_of_statement {ws0 : List Nat} {src : SolidCore.Verify.Generic.Source ws0}
    {c : TypeCheck.CheckedContract} {initcode code creation : ByteArray} {s : List (Nat × Nat)}
    (hc : src.checked = .ok c) (hb' : src.CreatedBy c initcode creation)
    (hl : Verify.Lifecycle.Statement src.fuel c initcode code ws0 s)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {b : Br} (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } src.fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T)
    (heq : Shapes.Equiv (solidCoreRuntime src.fuel) c code (Verify.LoopSource.Generic.SelCall sel fn ws)) :
    Deploys creation code s ∧
      SolidCore.Verify.Generic.EquivAt (src.semAt SolidCore.Verify.Generic.Context.default) c
        SolidCore.Verify.Generic.Context.default code (SelCallCov sel fn ws s) := by
  obtain ⟨d, hd⟩ := hl.source
  exact ⟨(SolidCore.Verify.Generic.Source.run_of_statement hc hb' hl).1,
    equivAt_of_runtime hd hsel hfind hw hret hb hT heq⟩

end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.equivAt_of_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.equivAt_of_statement
