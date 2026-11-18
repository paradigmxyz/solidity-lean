import SolidCore.Refinement.Generic.Stage

/-!
# The generic source stage for every caller

`Stage.lean`'s stages fix the caller: SolidCore's `Source.run` calls from `callerAddress` and the check
erases `msg.sender` to the constant `callerWord`. This module proves the stage once for every caller,
with the caller a symbolic word on both sides:

* `Source.runFrom a` is SolidCore's run of a call sent by the account `a` (the contract deployed, as in
  `Source.run`, by `callerAddress`); `Source.runFrom callerAddress` is `Source.run` (`runFrom_callerAddress`).
  `solidCoreFrom a` is its `Sem`.
* `eraseFnSym` erases a function with `msg.sender` as the symbolic word `WExpr.caller` (whose value is
  `Val.caller`), knowing that it fits in 160 bits (`callerFact`); the MIR side reads `caller` as the same
  word under `EnvFlags.allSym`.
* `checkSym` compares the two trees, once, for the symbolic caller; `stageFrom` gives, for every
  address `a < 2 ^ 160` and every oracle whose caller is `a` and whose Keccak-256 of two words is
  SolidCore's (`FromOk a o`), the stage from `solidCoreFrom a` to the module.
-/

namespace SolidCore.Refinement

namespace Source

open SolidCore.Solidity SolidCore.Solidity.Source

/-- SolidCore's result for `call` sent by `caller`: the contract constructed by `callerAddress` as in
`result?`, its storage replaced with the call's, and called through the ABI dispatcher from `caller`. -/
def resultFrom? (caller : Nat) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  let base := contract.core.context
  let context :=
    { base with sender := callerAddress, self := selfAddress, value := call.callvalue }
  match TypeCheck.CheckedContract.constructWithContext? fuel contract context
      State.empty selfAddress 0 [] with
  | some (CallResult.returned deployed _) =>
    let storage := call.storage.foldl
      (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) deployed.storage
    TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel contract context
      { deployed with storage := storage } selfAddress caller call.callvalue
      (call.calldata.data.toList.map (·.toNat))
  | _ => none

/-- Run `call`, sent by `caller`, against `contract` in SolidCore with `fuel`. -/
def runFrom (caller : Nat) (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    Option Observable :=
  (resultFrom? caller fuel contract call).map (observe call)

/-- From `callerAddress`, `runFrom` is `run`. -/
theorem runFrom_callerAddress (fuel : Nat) (contract : TypeCheck.CheckedContract) (call : Call) :
    runFrom callerAddress fuel contract call = run fuel contract call := rfl

/-! ### Construction with argument words -/

/-- The deployment of `contract` with the static argument words `ws`: the Lifecycle tier's
constructor call (`Verify.Lifecycle.DeployedAtWith` and `deployedAtWith` make exactly this call
on `Verify.Lifecycle.wordArgs ws`, `SolidCore.Refinement.Generic.Statement`): the constructor
in `Wide.ctxOf contract` from the empty state, sent by `selfAddress` with no value, on the
argument values `ws.map Value.word`. Its frame is the deployment's alone: it has no runtime
caller and no call, so a call's sender and value never reach it. -/
def deployArgs? (fuel : Nat) (ws : List Nat) (contract : TypeCheck.CheckedContract) :
    Option TypeCheck.CoreCallResult :=
  TypeCheck.CheckedContract.constructWithContext? fuel contract (Wide.ctxOf contract)
    State.empty selfAddress 0 (ws.map Value.word)

/-- SolidCore's result for `call` sent by `caller`, against `contract` deployed with the
argument words `ws` (`deployArgs?`): as `resultFrom?`, the deployed storage overwritten entry
by entry with the call's, then the ABI dispatcher from `caller` with the call's value. The
runtime context (`caller`, `call.callvalue`) and the deployment's (`selfAddress`, no value) are
separate arguments. With no words this is `resultFrom?` (`resultFromArgs?_nil`). -/
def resultFromArgs? (caller : Nat) (fuel : Nat) (ws : List Nat)
    (contract : TypeCheck.CheckedContract) (call : Call) :
    Option TypeCheck.CoreAbiCallResult :=
  let base := contract.core.context
  let context :=
    { base with sender := callerAddress, self := selfAddress, value := call.callvalue }
  match deployArgs? fuel ws contract with
  | some (CallResult.returned deployed _) =>
    let storage := call.storage.foldl
      (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) deployed.storage
    TypeCheck.CheckedContract.callCalldataAtFromWithContext? fuel contract context
      { deployed with storage := storage } selfAddress caller call.callvalue
      (call.calldata.data.toList.map (·.toNat))
  | _ => none

/-- With no argument words, `resultFromArgs?` is `resultFrom?`: the constructor overrides the
sender and value of the context it is given, so `resultFrom?`'s context and `Wide.ctxOf` give the
same constructor frame. -/
theorem resultFromArgs?_nil (caller fuel : Nat) (contract : TypeCheck.CheckedContract)
    (call : Call) :
    resultFromArgs? caller fuel [] contract call = resultFrom? caller fuel contract call :=
  rfl

/-- Run `call`, sent by `caller`, against `contract` deployed with the argument words `ws`. -/
def runFromArgs (caller : Nat) (fuel : Nat) (ws : List Nat) (contract : TypeCheck.CheckedContract)
    (call : Call) : Option Observable :=
  (resultFromArgs? caller fuel ws contract call).map (observe call)

/-- With no argument words, `runFromArgs` is `runFrom`. -/
theorem runFromArgs_nil (caller fuel : Nat) : runFromArgs caller fuel [] = runFrom caller fuel :=
  rfl

end Source

/-- SolidCore with fixed fuel, on calls sent by `caller`. -/
def solidCoreFrom (caller fuel : Nat) : Sem :=
  { Prog := SolidCore.Solidity.TypeCheck.CheckedContract, run := Source.runFrom caller fuel }

/-- From `callerAddress`, `solidCoreFrom` is `solidCore`. -/
theorem solidCoreFrom_callerAddress (fuel : Nat) : solidCoreFrom callerAddress fuel = solidCore fuel := rfl

/-- SolidCore with fixed fuel, on calls sent by `caller` to the contract deployed with the
argument words `ws`. -/
def solidCoreFromArgs (caller fuel : Nat) (ws : List Nat) : Sem :=
  { Prog := SolidCore.Solidity.TypeCheck.CheckedContract, run := Source.runFromArgs caller fuel ws }

/-- With no argument words, `solidCoreFromArgs` is `solidCoreFrom`. -/
theorem solidCoreFromArgs_nil (caller fuel : Nat) :
    solidCoreFromArgs caller fuel [] = solidCoreFrom caller fuel :=
  rfl

namespace Generic

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-! ## The erasure with a symbolic caller -/

/-- What the erasure knows of the symbolic caller: it fits in 160 bits. -/
def callerFact : WExpr × Bool := (.bin .gt .caller (.lit (2 ^ 160 - 1)), false)

theorem callerFact_eval (ρ : Val) (h : ρ.caller < 2 ^ 160) :
    (callerFact.1.eval ρ = 0 ↔ callerFact.2 = false) := by
  have h1 : ρ.caller < wordSize := Nat.lt_of_lt_of_le h (by decide)
  have h2 : (2 ^ 160 - 1 : Nat) < wordSize := by decide
  simp only [callerFact, WExpr.eval, BinOp.eval, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, iff_true]
  rw [if_neg (by omega)]
  rfl

/-- The state a call of `fn` starts in, with `msg.sender` the symbolic caller. -/
def initFrom (fn : FunctionDef) : SymState := { initState fn with caller := .caller }

/-- `eraseFn` with `msg.sender` the symbolic caller `WExpr.caller`, which the facts bound by
`2 ^ 160 - 1`. -/
def eraseFnSym (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) : Option Tree :=
  match widthsOf fn.params fn.paramAbiCleanups with
  | none => none
  | some ws =>
    if fn.returns.all wordBinding then do
      let b ← eraseStmt { E with facts := callerFact :: argFacts ws 0 } fuel fn.body (initFrom fn)
      let t ← brTree fn (callerFact :: argFacts ws 0) b
      some (paramGuards ws 0 t)
    else none

/-! ## SolidCore's run from any caller as the erased tree -/

theorem run_eq_at_from (a : Nat) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) (sel : Nat) (ws : List U256)
    (σ : List (Nat × Nat)) :
    Source.runFrom a fuel c (SolidCore.Refinement.Evm.Wide.callAt sel ws σ) =
      Option.map (Source.observe (SolidCore.Refinement.Evm.Wide.callAt sel ws σ))
        (ABI.Contract.callCalldataAtFromWithContext? fuel c.core (Wide.ctxOf c)
          { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress a 0
          ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  simp only [Source.runFrom, Source.resultFrom?, show (SolidCore.Refinement.Evm.Wide.callAt sel ws σ).callvalue = 0 from rfl,
    show (SolidCore.Refinement.Evm.Wide.callAt sel ws σ).storage = σ from rfl,
    show (SolidCore.Refinement.Evm.Wide.callAt sel ws σ).calldata = Abi.calldata sel (ws.map (·.toNat)) from rfl]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = Wide.ctxOf c from rfl, hc]
  simp only [TypeCheck.CheckedContract.callCalldataAtFromWithContext?, Dirty.bytes_calldata]


theorem run_rejected_from (a : Nat) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) (args : List Nat)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty)
    (σ : List (Nat × Nat)) :
    Source.runFrom a fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨s0, hdep⟩ := deployedStorage_of hd
  unfold Abi.deployedStorage at hdep
  dsimp only at hdep
  split at hdep
  case h_2 => simp at hdep
  rename_i deployed st hcons
  simp only [Source.runFrom, Source.resultFrom?, hcons,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, Dirty.bytes_calldata,
    Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length], hdec]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, Abi.rejected]
  simp


theorem source_run_clean_from (a : Nat) (ha : a < 2 ^ 160) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) {b : Br}
    (hb : eraseStmt { envOf c.core with facts := callerFact :: argFacts ws 0 } fuel fn.body (initFrom fn) = some b)
    {T : Tree} (hT : brTree fn (callerFact :: argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word)) :
    Source.runFrom a fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, a⟩).obs := by
  rw [SolidCore.Refinement.Wide.callAt_of_args sel args hargs σ,
    run_eq_at_from a hd, SolidCore.Refinement.Wide.map_ofNat_toNat args hargs]
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
  set ρ : Val := ⟨args, slotValue σ, solHash, a⟩ with hρ
  have hρok : ρ.Ok := slotValue_store σ
  set K : Facts := callerFact :: argFacts ws 0 with hK
  have hKρ : K.Hold ρ := (argFacts_hold ρ hargs ws 0 (by simpa [hρ] using hclean)).cons (callerFact_eval ρ ha)
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
        have := getD_storage_cover hd hcov k
        subst hst
        simp only [State.loadSlot, StorageMap.lookup?, initFrom, initState, Writes.store, hρ]
        rw [← this]
        simp only [SolidCore.Solidity.Shared.norm, modulus_eq, Std.HashMap.get?_eq_getElem?]
        cases (List.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage σ)[k % wordSize]? <;> rfl
      logs := by subst hst; simp [hd.events, initFrom, initState]
      facts := hKρ }
  obtain ⟨r, hrun, hleaf⟩ := eval_stmt ρ E ctx fuel fn.body (initFrom fn) b hb _ hrel
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
        ABI.Contract.encodeRevertData?, Source.observe, Tree.eval, Res.obs, hρ,
        SolidCore.Refinement.Evm.Wide.callAt]
    | panic c =>
      simp only [leafTree, Option.some.injEq] at hT'
      subst hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_panic ρ,
        Source.observe, Tree.eval, Res.obs, hρ, SolidCore.Refinement.Evm.Wide.callAt]
    | error m =>
      simp only [leafTree, Option.map_eq_some_iff] at hT'
      obtain ⟨bs, hbs, rfl⟩ := hT'
      simp [FunctionDef.callBodyResult, RevertData.untagFixedBytes, Fail.data, encode_error ρ _ hbs,
        Source.observe, Tree.eval, Res.obs, hρ, SolidCore.Refinement.Evm.Wide.callAt]


theorem source_run_from (a : Nat) (ha : a < 2 ^ 160) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFnSym (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.runFrom a fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, a⟩).obs := by
  unfold eraseFnSym at hT
  split at hT
  · simp at hT
  rename_i ws hw
  split at hT
  case isFalse => simp at hT
  rename_i hret
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hT
  obtain ⟨b, hb, t, ht, rfl⟩ := hT
  rw [paramGuards_eval ⟨args, slotValue σ, solHash, a⟩ t hargs ws 0, List.drop_zero]
  have hdec := decode_args hw args hlen hargs
  by_cases hclean : argsClean ws args = true
  · rw [if_pos hclean]
    rw [if_pos hclean] at hdec
    exact source_run_clean_from a ha hd hcov hsel hfind hw hret hb ht args hlen hargs hclean hdec
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [run_rejected_from a hd hsel hfind args hdec σ]
    rfl


/-! ## The check and the stage for every caller -/

/-- `checkFn` with the symbolic caller on both sides. -/
def checkFnSym (fuel mirFuel : Nat) (core : Contract) (m : Module) (f : Fn) : Bool :=
  decide (f.sel < 2 ^ 32) &&
    match core.findFunctionBySelector? f.sel with
    | none => false
    | some fn =>
      decide (fn.params.length = f.params.length) &&
        match eraseFnSym (envOf core) fuel fn, symTree m f.sel f.params.length mirFuel .allSym with
        | some t1, some t2 => t1.canon.beq t2.canon
        | _, _ => false

/-- Whether every function of `fns` lowers to `m` for the symbolic caller. -/
def checkSym (fuel mirFuel : Nat) (core : Contract) (m : Module) (fns : List Fn) : Bool :=
  fns.all (checkFnSym fuel mirFuel core m)

/-- What the stage for the caller `a` asks of the oracle: its caller is `a` and its Keccak-256 of two
words is SolidCore's slot hash (`HashOk`). -/
structure FromOk (a : Nat) (o : Oracle) : Prop where
  caller : (o.caller.setWidth 256).toNat = a
  hash : HashOk o

theorem FromOk.envAsk {a : Nat} {o : Oracle} (h : FromOk a o) (ha : a < 2 ^ 160) (args : List Nat)
    (store : Nat → Nat) : EnvAsk .allSym o ⟨args, store, solHash, a⟩ :=
  ⟨fun _ => by
    have : a < wordSize := Nat.lt_of_lt_of_le ha (by decide)
    simp [EnvFlags.callerExpr, EnvFlags.allSym, WExpr.eval, h.caller, Nat.mod_eq_of_lt this],
   fun _ => h.hash⟩

/-- The call facts do not read the caller. -/
theorem callFactsFrom (sel : Nat) (hsel : sel < 2 ^ 32) (args : List Nat)
    (hargs : ∀ a ∈ args, a < 2 ^ 256) (σ : List (Nat × Nat)) (a : Nat) :
    CallFacts sel args.length ⟨args, slotValue σ, solHash, a⟩
      { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } :=
  have h := callFacts sel hsel args hargs σ
  ⟨h.value, h.size, h.args, h.selector, h.store, h.ok⟩

/-- **The generic source stage for every caller**: a checked contract whose constructor leaves the
storage entries `s` and no logs and a lowered MIR module that `checkSym` accepts give, for every
address `a < 2 ^ 160` and every oracle whose caller is `a` and whose Keccak-256 of two words is
SolidCore's, the stage from SolidCore's run sent by `a` to the module's lowered MIR semantics, on
every call of a function of `fns` on any argument words below `2 ^ 256`, with no value, from any
storage that writes every slot of `s`. -/
theorem stageFrom (a : Nat) (ha : a < 2 ^ 160) (o : Oracle) (ho : FromOk a o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : checkSym fuel mirFuel c.core m fns = true) :
    Stage (solidCoreFrom a fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkFnSym at hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFnSym (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTree m f.sel f.params.length mirFuel .allSym with
  | none => simp [hfind, ht1, ht2] at hcf
  | some t2 =>
  simp only [hfind, ht1, ht2, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, hcf⟩ := hcf
  have hcf := Tree.eq_of_beq hcf
  have hsrc := source_run_from a ha hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs
  change Source.runFrom a fuel c _ = some obs at hrun
  rw [hsrc] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTree_sound (callFactsFrom f.sel hsel args hargs σ a) o m (ho.envAsk ha _ _) ht2,
    ← Tree.eval_canon, ← hcf, Tree.eval_canon]

/-- `stageFrom` from the deployed storage `s`. -/
theorem stageDeployedFrom (a : Nat) (ha : a < 2 ^ 160) (o : Oracle) (ho : FromOk a o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : checkSym fuel mirFuel c.core m fns = true) :
    Stage (solidCoreFrom a fuel) (moduleSem o) c m (fullScope fns s) :=
  SolarTV.Stage.mono (stageFrom a ha o ho hd hchk) fun _ h => ⟨s, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- Every valid call has a source result from the caller `a`: the source half of `stageFrom`. -/
theorem definedFrom (a : Nat) (ha : a < 2 ^ 160) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : checkSym fuel mirFuel c.core m fns = true) :
    ∀ call, (∃ σ, Covers s σ ∧ fullScope fns σ call) → ((solidCoreFrom a fuel).run c call).isSome := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkFnSym at hcf
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFnSym (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTree m f.sel f.params.length mirFuel .allSym with
  | none => simp [hfind, ht1, ht2] at hcf
  | some t2 =>
  simp only [hfind, ht1, ht2, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  have hsrc := source_run_from a ha hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs
  change (Source.runFrom a fuel c _).isSome = true
  rw [hsrc]
  rfl

end Generic

end SolidCore.Refinement
