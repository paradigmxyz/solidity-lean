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
    (hb' : src.CreatedBy initcode creation)
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
  exact ⟨(SolidCore.Verify.Generic.Source.run_of_statement hb' hl).1,
    equivAt_of_runtime hd hsel hfind hw hret hb hT heq⟩

end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.equivAt_of_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.equivAt_of_statement
