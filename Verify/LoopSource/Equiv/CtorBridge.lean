import SolidCore.Refinement.Generic.Statement
import SolidCore.Refinement.Generic.LoopRun
import Verify.LoopSource.Generic.Statement
import SolidCore.Refinement.Solar.AssembleCtxGasFrom

/-!
# From the runtime code to the deployed source: the constructor-argument bridge

`Source.semAt` (`Verify/Generic/Expected.lean`) runs a call against the contract SolidCore's
constructor leaves on the source's argument words (`solidCoreFromArgs`); `loop_equiv` gives
`Shapes.Equiv` over the runtime code alone (`solidCoreRuntime`). This module relates them, exactly:

* **Entry state.** A constructor that returns a state `d` with no logs (`LoadDeployed`, which the
  lifecycle statement's `DeployedAtWith` gives: `loadDeployed_of`) makes the source's run of a call
  the ABI dispatcher on `d` with the call's storage written over `d.storage`
  (`resultFromArgs?_of_cons`); the runtime code's is the same dispatcher, context and caller on the
  empty state with the call's storage.
* **Storage, collisions, precedence.** `getD_load_cover`: every slot of that entry state reads
  `slotValue σ` (the call's storage, the last write of a key winning, keys mod `2 ^ 256`) when the
  call writes every slot `d` leaves nonzero (`CoversLoad d σ`, which `Covers s σ` gives under
  `DeployedAtWith`: `coversLoad_of`). Without it a slot the call does not write reads the
  constructor's value on the source side and 0 on the runtime side, and the two runs can differ, so
  the cover is the bridge's premise on the call.
* **Other state fields.** None is assumed: a body's run (`BodyRuns`) holds from every runtime its
  relation (`StmtRel`) admits, whatever the constructor left in transient storage or immutables;
  its logs are `d.events`, which the lifecycle statement makes `[]`.
* **Constructor failure.** A constructor that does not return leaves no run
  (`runFromArgs_eq_none`), so no Equiv over `semAt` holds of a reverting deployment unless every
  bytecode result is inert.

`deployed_run_entry_at` runs a call from the deployed state to its tree's observable, for any caller
word the body's first state erases `msg.sender` to. `semAt_eq_runtime` makes the two runs equal on a
call of a loop-carrying function, and `equivAt_of_runtime` turns the runtime code's `Shapes.Equiv`
into `EquivAt (src.semAt Context.default)` on the valid calls whose storage covers the deployment.

**Fixed-context evidence only.** The caller is `callerAddress` (`Context.default`): the loop route's
`BodyRuns` is stated for the initial state whose `msg.sender` is the constant `callerWord`
(`initState`), and `loop_equiv`'s chain runs the bytes from `callerAddress`. Every other caller and
every call value stay OPEN. Counter stays outside the accepted subset.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic

/-! ## Load-level deployment (fixed context; NOT `DeployedAtWith`)

`LoadDeployed`: SolidCore's constructor on the words returns a state `d`, with no logs. It says
nothing of `d.storage`'s entry list; facts about `d`'s storage are stated through its loads.
`loadDeployed_of`: the lifecycle statement's `DeployedAtWith` gives it, with every load the value
`s` gives at the slot, so this route is strictly more general than the exact one. -/

/-- The constructor on `ws` returns `d`, with no logs. -/
structure LoadDeployed (fuel : Nat) (c : TypeCheck.CheckedContract) (ws : List Nat) (d : Source.State) : Prop where
  cons : ∃ vs, Refinement.Source.deployArgs? fuel ws c = some (CallResult.returned d vs)
  events : d.events = []

/-- The value the entry list `s` gives at slot `q`: its first entry's, else 0. -/
def sAt (s : List (Nat × Nat)) (q : Nat) : Nat := ((s.find? (fun kv => kv.1 == q)).map (·.2)).getD 0

/-- **The load cover**: the call writes every slot `d` leaves nonzero. -/
def CoversLoad (d : Source.State) (σ : List (Nat × Nat)) : Prop :=
  ∀ k, d.loadSlot k ≠ 0 → ∃ kv ∈ σ, kv.1 % wordSize = k % wordSize

theorem loadSlot_eq_getD (d : Source.State) (k : Nat) :
    d.loadSlot k = (d.storage[k % 2 ^ 256]?).getD 0 := by
  simp only [State.loadSlot, StorageMap.lookup?, SolidCore.Solidity.Shared.norm, modulus_eq,
    Std.HashMap.get?_eq_getElem?]
  generalize d.storage[k % 2 ^ 256]? = o
  cases o <;> rfl

/-- Under `DeployedAtWith`, a call writing every key the constructor wrote writes every slot it left
nonzero. -/
theorem coversLoad_of {fuel : Nat} {args : List TypeCheck.CoreValue} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c args d s)
    {σ : List (Nat × Nat)} (hcov : Covers s σ) : CoversLoad d σ := by
  intro k hk
  rw [loadSlot_eq_getD] at hk
  generalize hq : k % 2 ^ 256 = q at hk
  cases h : d.storage[q]? with
  | none => simp [h] at hk
  | some v =>
    obtain ⟨kv', hkv', he⟩ := hcov _ (hd.storage ▸ Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h)
    exact ⟨kv', hkv', by rw [he, ← hq]; exact Nat.mod_mod _ _⟩

/-- **The exact route gives the load-level one**: `DeployedAtWith` gives `LoadDeployed`, every load
the value `s` gives at the slot mod `2 ^ 256`, and `Covers s` the load cover. -/
theorem loadDeployed_of {fuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws) d s) :
    LoadDeployed fuel c ws d ∧ (∀ k, d.loadSlot k = sAt s (k % 2 ^ 256)) ∧
      ∀ σ, Covers s σ → CoversLoad d σ := by
  refine ⟨⟨hd.cons, hd.events⟩, fun k => ?_, fun _ => coversLoad_of hd⟩
  rw [loadSlot_eq_getD, sAt, ← hd.storage]
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

/-- What a run shows on `σ`: a failure leaves the call's own storage (`Source.observe`). -/
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

/-- **From a load-level deployment, a call sent by `a`** of a loop-carrying function whose body
runs from the first state with `msg.sender` erased to `e` (the word `a` at the call) runs to
the tree's observable at the entry storage's loads `store`, whatever the call writes. -/
theorem deployed_run_entry_at (a : Nat) {e : WExpr} {fuel : Nat} {ws0 : List Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {store : Nat → Nat}
    (hstore : ∀ k, ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 = store k)
    (hok : ∀ k, store (k % wordSize) % wordSize = store k)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all retBinding = true) (htags : tagsOk fn = true) {b : Br}
    (hb : ∀ ρ ctx rt, StmtRel ρ { envOf c.core with facts := argFacts ws 0 } ctx rt
        { initState fn with caller := e } →
      ∃ r, Stmt.eval fuel c.core.table ctx rt fn.body = .done (.ok r) ∧
        LeafRel ρ { envOf c.core with facts := argFacts ws 0 } ctx r (b.eval ρ))
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (he : SolidCore.Solidity.Shared.norm a = e.eval ⟨args, store, solHash, a⟩)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      .ok (tyVals (fn.params.map BindingDecl.ty) args)) :
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
  have hr : ∀ r ∈ fn.returns, retBinding r = true := fun r hr => List.all_eq_true.mp hret r hr
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
  have htg := tagsOk_spec htags
  have hframe : fn.initialFrame? (argVals (fn.params.map BindingDecl.ty) args) =
      some (frameOfT ρ (fnTags fn)
        (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 : BindingDecl.bindArgs? fn.params (argVals (fn.params.map BindingDecl.ty) args) =
        some (frameOfT ρ (fnTags fn) (paramLocals fn.params 0)) :=
      bindArgs_clean ρ hargs (fnTags fn) fn.params fn.paramAbiCleanups ws 0 hw
        (by simpa [hρ] using hclean) (by simp [hρ, hlen]) htg.1
    have hd : fn.returns.map BindingDecl.defaultBinding =
        frameOfT ρ (fnTags fn) (fn.returns.map fun r => (r.name, WExpr.lit 0)) := by
      exact defaults_typed ρ (fnTags fn) fn.returns hr htg.2
    have happ : ∀ (A B : Locals), frameOfT ρ (fnTags fn) (A ++ B) =
        frameOfT ρ (fnTags fn) A ++ frameOfT ρ (fnTags fn) B := by
      intro A B; simp [frameOfT, List.map_append]
    simp only [FunctionDef.initialFrame?, h0, FunctionDef.returnDefaultBindings, ← hd, happ]
  have hrel : StmtRel ρ E ctx
      { state := { st0 with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOfT ρ (fnTags fn)
          (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] }
      { initState fn with caller := e } :=
    { fields := by subst hctx; rfl
      events := by subst hctx; rfl
      checked := by subst hctx; rfl
      sender := by subst hctx; exact he
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
      facts := hKρ
      mem := fun _ _ hl => by simp [initState] at hl
      next := fun k hk => by simp only [initState, Option.some.injEq] at hk; subst hk; rfl }
  obtain ⟨r, hrun, hleaf⟩ := hb ρ ctx _ hrel
  have hcall : fn.call? fuel c.core.table ctx st0 (argVals (fn.params.map BindingDecl.ty) args) =
      some (fn.callBodyResult st0 r) := by
    have hacc' : fn.acceptsValue ctx.value = true := hctxv ▸ hacc
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, hacc', hframe,
      if_true, Option.map_some, Option.bind_some]
    rw [hrun]
    rfl
  have hcallT : fn.call? fuel c.core.table ctx st0 (tyVals (fn.params.map BindingDecl.ty) args) =
      some (fn.callBodyResult st0 r) := by
    rw [← hcall]
    simp only [FunctionDef.call?, call_tyVals hw hlen hargs]
  obtain ⟨T', hT', hTe⟩ := brTree_eval fn K ρ b T hT
  rw [hacc, if_pos rfl, hcallT, ← hTe]
  generalize b.eval ρ = l at hT' hleaf
  rcases l with S | ⟨S, _ | ⟨v, vs⟩, ts⟩ | p <;> cases r <;> simp only [LeafRel] at hleaf <;>
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
    simp only [FunctionDef.callBodyResult, retVals_nil_vals, List.map_nil, List.isEmpty_nil, ↓reduceIte,
      FunctionDef.collectReturns, collectReturnBindings,
      collect_vals ρ rt S hKρ hleaf fn.returns ws hok hws, untag_vals ρ _ ws hKρ hok,
      encode_vals ρ hKρ fn.returns _ ws hok, bind, Option.bind]
    simp only [fixObs, Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
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
    have hne : (retVals ρ ts (v :: vs)).isEmpty = false := by cases ts <;> rfl
    simp only [FunctionDef.callBodyResult, hne, Bool.false_eq_true, ↓reduceIte,
      FunctionDef.coerceReturnValues, coerceReturnBindings,
      coerce_vals ρ rt hKρ fn.returns ts (v :: vs) hok, untag_vals ρ ts (v :: vs) hKρ hok,
      encode_vals ρ hKρ fn.returns ts (v :: vs) hok, bind, Option.bind]
    simp only [fixObs, Source.observe, Tree.eval, Res.obs, ↓reduceIte, logEntries_map,
      hleaf.logs, Option.some.injEq, Observable.mk.injEq, true_and]
    funext slot
    exact loadSlot_eq _ S.writes ρ hρok hleaf.store slot
  · subst hleaf
    rcases p with _ | c | m <;> simp only [leafTree, Option.some.injEq, Option.map_eq_some_iff] at hT'
    · subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data,
        ABI.Contract.encodeRevertData?, fixObs, Source.observe, Tree.eval, Res.obs, hρ]
    · subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        fixObs, Source.observe, Tree.eval, Res.obs, hρ]
    · obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        fixObs, Source.observe, Tree.eval, Res.obs, hρ]

/-- **From a load-level deployment**, a call of a loop-carrying function runs to the tree's
observable at the entry storage's loads `store`, whatever the call writes. -/
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
      some (fixObs σ (T.eval ⟨args, store, solHash, callerWord⟩).obs) :=
  deployed_run_entry_at callerAddress hd hstore hok hsel hfind (widthsOf_T hw).1 (retBinding_of_word hret)
    (tagsOk_of_words (words_of_widths hw hret)) hb hT args rfl hlen hargs hclean
    (by rw [tyVals_params hw hlen]; exact hdec)

/-- **From a load-level deployment**, a call of a function of the generic source stage (typed
parameters included) runs to the tree's observable at the entry storage's loads. -/
theorem deployed_run_entryT {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)} {store : Nat → Nat}
    (hstore : ∀ k, ((σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?).getD 0 = store k)
    (hok : ∀ k, store (k % wordSize) % wordSize = store k)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all retBinding = true) (htags : tagsOk fn = true) {b : Br}
    (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      .ok (tyVals (fn.params.map BindingDecl.ty) args)) :
    Refinement.Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (fixObs σ (T.eval ⟨args, store, solHash, callerWord⟩).obs) :=
  deployed_run_entry_at callerAddress hd hstore hok hsel hfind hw hret htags hb hT args rfl hlen hargs
    hclean hdec

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

/-- **Load-level `semAt_eq_runtime`** (fixed context; NOT `DeployedAtWith`). -/
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


/-- **On a covering call of a loop-carrying function, the source deployed with `ws0` and the
runtime code run alike**, both to the function's tree. -/
theorem semAt_eq_runtime {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs ws0) d s)
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws) (hret : fn.returns.all wordBinding = true)
    {b : Br} (hb : BodyRuns { envOf c.core with facts := argFacts ws 0 } fuel fn b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) {call : Call}
    (hv : SelCallCov sel fn ws s call) :
    (solidCoreFromArgs callerAddress fuel ws0).run c call = (solidCoreRuntime fuel).run c call :=
  semAt_eq_runtime_load (loadDeployed_of hd).1 hsel hfind hw hret hb hT ⟨hv.1, coversLoad_of hd hv.2⟩

/-- **The runtime code's equivalence is the deployed source's**, in `Context.default`, on the valid
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

/-- **From the lifecycle statement**: the same, with the deployment named by `run_of_statement`'s
premises (`hb`: the creation code carries the source's words; `hl`: the lifecycle statement). -/
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
