import Verify.ShapeGeneric
import Verify.LoopSource.Equiv.CtorBridge
import SolidCore.Refinement.Generic.CtorAll

/-!
# The generic source stage for a constructor with static word parameters, for every argument

`Generic.stageAtValueWith`, `Generic.definedAtValue` and `Shapes.compiled` take `Wide.DeployedAt`:
SolidCore's constructor run with **no arguments** (`Source.run`). A constructor with parameters has
no such run. This module states the same stage, definedness and shape for the source deployed with
argument words `ws` (`solidCoreFromArgs callerAddress fuel ws`, `StageFrom.lean`: the constructor
on `ws.map Value.word`, then the call from the state it leaves with the call's storage written
over it):

* `source_run_args`, `run_rejected_args`, `source_run_value_args`: a call of a function of the
  fragment runs as its erased tree, rejects dirty words, and rejects a value, from a load-level
  deployment (`Loop.LoadDeployed`: the constructor returns `d` with no logs) and a call storage that
  writes every slot `d` leaves nonzero (`Loop.CoversLoad`), as `source_run` does from `DeployedAt`.
* `stageAtValueArgs`, `definedAtValueArgs` and `Shapes.compiledArgs`: the stage, definedness and
  `Compiled` on `genericValid fns s`, for every `s` whose cover gives the load cover.
* `construct_of_erase`: SolidCore's constructor on **every** list of argument words runs as one
  erasure of its body (`eraseStmt`, with the parameters' width facts), the tree `b` over the words.
  `loadDeployed_of_normals`: when every leaf of `b` is normal with the writes `W` and no logs, or a
  revert (`normalsOnly`), then on each argument list on which the constructor returns it leaves a
  state with no logs whose every slot loads what `W` gives at those words; `returns_of_eval`: it
  returns wherever `b`'s leaf is normal (always, for a tree that is one normal leaf).
  `coversLoad_of_writes`: a storage that writes every key of `W` (`storageOf`) gives the load cover.
* `CtorReturns fuel c? ws`: the checked contract's constructor returns on `ws`, the premise of a
  statement about a constructor that may revert for some arguments.
* `ctorShapeOf` and `deployed_of_ctorShapeOf`: what a generated module evaluates once in the kernel
  (the checked core, and whether the constructor's erasure is the printed tree with the printed
  writes), and the deployment for every argument list it gives.

Not covered here: parameters other than `uint256`-typed words (narrow `uintN` with its cleanup
included) and `address` (`bindArgs_words`); a constructor whose erasure is undefined (for one, a
write to a storage field other than an unsigned scalar or mapping), whose normal leaves differ, log
or return; immutables (their runtime bytes depend on the arguments); the creation bytecode (the
statement is about the runtime bytecode, as the no-argument route's is).
-/

namespace SolidCore.Refinement.Generic

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-! ## Calls of the contract deployed with argument words -/

/-- **Dirty argument words revert**, against the contract deployed with `ws0`. -/
theorem run_rejected_args {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} (hd : Loop.LoadDeployed fuel c ws0 d) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) (args : List Nat)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty)
    (σ : List (Nat × Nat)) :
    Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) := by
  obtain ⟨vs, hcons⟩ := hd.cons
  simp only [Source.runFromArgs, Source.resultFromArgs?, hcons,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, Dirty.bytes_calldata,
    Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length], hdec]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, Abi.rejected]
  simp

/-- **A call of a function of the fragment runs as its erased tree**, against the contract deployed
with `ws0`, from any storage that writes every slot the deployment leaves nonzero. -/
theorem source_run_args {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} (hd : Loop.LoadDeployed fuel c ws0 d) {σ : List (Nat × Nat)}
    (hcov : Loop.CoversLoad d σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold eraseFn at hT
  split at hT
  · simp at hT
  rename_i ws hw
  split at hT
  case isFalse => simp at hT
  rename_i hret'
  obtain ⟨hret, htags⟩ := Bool.and_eq_true _ _ ▸ hret'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hT
  obtain ⟨b, hb, t, ht, rfl⟩ := hT
  rw [paramGuards_eval ⟨args, slotValue σ, solHash, callerWord⟩ t hargs ws 0, List.drop_zero]
  have hdec := decode_argsT hw args hlen hargs
  by_cases hclean : argsClean ws args = true
  · rw [if_pos hclean]
    rw [if_pos hclean] at hdec
    rw [Loop.deployed_run_entryT hd (Loop.getD_load_cover hcov) (slotValue_store σ) hsel hfind hw
      hret htags (Loop.bodyRuns_of_erase hb) ht args hlen hargs hclean hdec, Loop.fixObs_slotValue]
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [run_rejected_args hd hsel hfind args hdec σ]
    rfl

/-- **A value is rejected**, against the contract deployed with `ws0`: a call of a non-payable
function with a value other than 0 reverts with empty output and leaves the storage. -/
theorem source_run_value_args {fuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} (hd : Loop.LoadDeployed fuel c ws0 d) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    {ws : List Nat} (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hpay : fn.payable = false) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) {v : Nat}
    (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    Source.runFromArgs callerAddress fuel ws0 c
        { calldata := Abi.calldata sel args, callvalue := v, storage := σ } =
      some (rejected σ) := by
  obtain ⟨vs, hcons⟩ := hd.cons
  have hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
        .ok (tyVals (fn.params.map BindingDecl.ty) args) ∨
      ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty := by
    rw [decode_argsT hw args hlen hargs]
    by_cases hclean : argsClean ws args = true
    · exact Or.inl (if_pos hclean)
    · exact Or.inr (if_neg hclean)
  have hvm : v % SolidCore.Solidity.Shared.wordModulus = v := Nat.mod_eq_of_lt hv
  have hacc : fn.acceptsValue v = false := by
    simp [FunctionDef.acceptsValue, hpay, wordEq, SolidCore.Solidity.Shared.norm, hvm, hv0]
  simp only [Source.runFromArgs, Source.resultFromArgs?, hcons,
    TypeCheck.CheckedContract.callCalldataAtFromWithContext?,
    ABI.Contract.callCalldataAtFromWithContext?, Dirty.bytes_calldata,
    Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop ABI.selectorBytes =
      Dirty.argBytes args by simp [ABI.selectorBytes, natToBytes_length]]
  rcases hdec with hdec | hdec <;> rw [hdec] <;>
    simp only [hacc, Bool.false_eq_true, ↓reduceIte, ABI.Contract.rejectedValueCall?,
      ABI.Contract.revertedEmptyCall?, ABI.Contract.revertedCall?,
      ABI.Contract.encodeRevertData?, bind, Option.bind, Option.map_some, Source.observe,
      rejected]

/-! ## The stage -/

/-- **The generic source stage at every value, for the contract deployed with `ws0`**: as
`stageAtValueWith`, from a load-level deployment whose every cover of `s` is a load cover. -/
theorem stageAtValueArgs (o : Oracle) {fuel mirFuel : Nat} {ws0 : List Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : Loop.LoadDeployed fuel c ws0 d) (hcov : ∀ σ, Covers s σ → Loop.CoversLoad d σ)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Stage (solidCoreFromArgs callerAddress fuel ws0) (moduleSem o) c m
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hc, hv, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, ht2, hcf⟩ := check_mem hchk hf
  change Source.runFromArgs callerAddress fuel ws0 c _ = some obs at hrun
  by_cases hv0 : v = 0
  · subst hv0
    rw [source_run_args hd (hcov σ hc) hsel hfind ht1 args (by rw [hlen, hpl]) hargs] at hrun
    cases hrun
    rw [← hlen] at ht2
    rw [symTree_sound (callFacts f.sel hsel args hargs σ) o m (henv.envAsk _ _) ht2,
      ← Tree.eval_of_agree hcf]
  obtain ⟨hpay, T, ht2', hrev⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  rw [source_run_value_args hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ] at hrun
  cases hrun
  rw [← hlen] at ht2'
  rw [symTreeValue_sound (callFactsFromValue f.sel hsel args hargs σ callerWord hv0 hv) o m
    (henv.envAsk _ _) ht2', Tree.eval_revertsEmpty _ _ hrev]
  rfl

/-- **SolidCore finishes every call of the scope**, against the contract deployed with `ws0`. -/
theorem definedAtValueArgs {fuel mirFuel : Nat} {ws0 : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Loop.LoadDeployed fuel c ws0 d)
    (hcov : ∀ σ, Covers s σ → Loop.CoversLoad d σ) {m : Module} {fns : List Fn}
    {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Defined (solidCoreFromArgs callerAddress fuel ws0) c
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hc, hv, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, -, -⟩ := check_mem hchk hf
  change (Source.runFromArgs callerAddress fuel ws0 c _).isSome = true
  by_cases hv0 : v = 0
  · subst hv0
    rw [source_run_args hd (hcov σ hc) hsel hfind ht1 args (by rw [hlen, hpl]) hargs]
    rfl
  obtain ⟨hpay, -, -, -⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  rw [source_run_value_args hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ]
  rfl

/-! ## The deployment for every argument list -/

/-- The entries the writes `W` leave at the argument words `ws`: each key and value word. -/
def storageOf (W : Writes) (ws : List Nat) : List (Nat × Nat) :=
  W.map fun w => (w.1.eval ⟨ws, fun _ => 0, solHash, callerWord⟩,
    w.2.eval ⟨ws, fun _ => 0, solHash, callerWord⟩)

theorem store_ne_zero {ρ : Val} (hz : ∀ n, ρ.store n = 0) :
    ∀ (W : Writes) (k : Nat), Writes.store ρ W k ≠ 0 → ∃ w ∈ W, w.1.eval ρ = k % wordSize
  | [], k, h => absurd (hz k) h
  | w :: W, k, h => by
    simp only [Writes.store] at h
    split at h
    · rename_i he; exact ⟨w, List.mem_cons_self .., he⟩
    · obtain ⟨w', hw', he⟩ := store_ne_zero hz W k h
      exact ⟨w', List.mem_cons_of_mem _ hw', he⟩

/-- **A storage that writes every key of the writes gives the load cover.** -/
theorem coversLoad_of_writes {d : Source.State} {W : Writes} {ws : List Nat}
    (hl : ∀ k, d.loadSlot k = Writes.store ⟨ws, fun _ => 0, solHash, callerWord⟩ W k)
    {σ : List (Nat × Nat)} (hcov : Covers (storageOf W ws) σ) : Loop.CoversLoad d σ := by
  intro k hk
  rw [hl] at hk
  obtain ⟨w, hw, he⟩ := store_ne_zero (fun _ => rfl) W k hk
  obtain ⟨kv', hm, hkv⟩ := hcov _ (List.mem_map_of_mem hw)
  refine ⟨kv', hm, ?_⟩
  rw [hkv]
  simp only at he ⊢
  rw [he, Nat.mod_mod]

/-! ## The constructor on every argument list -/

theorem callBodyResult_normal {fn : FunctionDef} (hret0 : fn.returns = []) (rt : Runtime) :
    fn.callBodyResult State.empty (.normal rt) = .returned rt.state [] := by
  have hcr : fn.collectReturns rt = .ok [] := by
    unfold FunctionDef.collectReturns; rw [hret0]; rfl
  simp only [FunctionDef.callBodyResult, hcr, List.map_nil]

/-- **SolidCore's constructor on an argument list runs as its body's erasure**: for each list of
words of the parameters' count, below `2 ^ 256` and clean for the parameters' widths, the
constructor's call result is its body's result, which the erasure's leaf at those words describes. -/
theorem construct_of_erase {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br}
    (herase : eraseStmt { envOf c.core with facts := argFacts wds 0 } fuel fn.body
      { initState fn with caller := .lit selfAddress } = some b)
    {ws : List Nat} (hlen : ws.length = fn.params.length) (hargs : ∀ a ∈ ws, a < 2 ^ 256)
    (hclean : argsClean wds ws = true) :
    ∃ ctx r, Source.deployArgs? fuel ws c = some (fn.callBodyResult State.empty r) ∧
      LeafRel ⟨ws, fun _ => 0, solHash, callerWord⟩ { envOf c.core with facts := argFacts wds 0 }
        ctx r (b.eval ⟨ws, fun _ => 0, solHash, callerWord⟩) := by
  set ρ : Val := ⟨ws, fun _ => 0, solHash, callerWord⟩ with hρ
  have hρok : ρ.Ok := fun _ => rfl
  let E : EraseEnv := { envOf c.core with facts := argFacts wds 0 }
  set ctx : Context := { Wide.ctxOf c with sender := selfAddress, value := 0, construction := true, selfDispatch? := some (ABI.selfDispatchHook fuel c.core 0) } with hctx
  have hargs' : ∀ a ∈ ρ.args, a < Generic.wordSize := hargs
  have hframe : fn.initialFrame? (ws.map Value.word) =
      some (frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 := bindArgs_words ρ hargs' fn.params 0 hps (by simp [hρ, hlen])
    simp only [FunctionDef.initialFrame?, List.drop_zero] at h0 ⊢
    rw [h0]
    simp [hret0, FunctionDef.returnDefaultBindings]
  have hrel : StmtRel ρ E ctx
      { state := { State.empty with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOf ρ (paramLocals fn.params 0 ++ fn.returns.map fun r => (r.name, .lit 0))] }
      { initState fn with caller := .lit selfAddress } :=
    { fields := rfl, events := rfl, checked := rfl
      sender := rfl
      hash := rfl
      ok := hρok
      frames := by
        simp [initState, paramTags_words (fun p hp => by rcases (hps p hp).1 with h | h <;> simp [h, tagOf])]
      store := by
        intro k _
        simp [State.loadSlot, StorageMap.lookup?, State.empty, Writes.store, initState, hρ]
      logs := by simp [State.empty, initState]
      facts := argFacts_hold ρ hargs' wds 0 (by simpa [hρ] using hclean) }
  obtain ⟨r, hrun, hleaf⟩ := eval_stmt ρ E ctx fuel fn.body _ _ herase _ hrel
  refine ⟨ctx, r, ?_, hleaf⟩
  have hacc : fn.acceptsValue 0 = true := by
    simp [FunctionDef.acceptsValue, wordEq]
  show TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c) State.empty
    selfAddress 0 (ws.map Value.word) = _
  simp only [TypeCheck.CheckedContract.constructWithContext?, hf, Option.bind_eq_bind,
    Option.bind_some]
  simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, ← hctx, hacc,
    hframe, if_true, Option.map_some]
  rw [show c.core.table = E.tbl from rfl, hrun]
  rfl

/-- Whether every leaf of the constructor's erasure is a normal leaf with the writes `W` and no
logs, or a revert. -/
def normalsOnly (W : Writes) : Br → Bool
  | .leaf (.normal S) => S.writes == W && S.logs.isEmpty
  | .leaf (.reverted _) => true
  | .leaf (.returned _ _) => false
  | .ite _ t e => normalsOnly W t && normalsOnly W e

theorem normalsOnly_eval {W : Writes} (ρ : Val) : ∀ {b : Br}, normalsOnly W b = true →
    (∃ S, b.eval ρ = .normal S ∧ S.writes = W ∧ S.logs = []) ∨ ∃ f, b.eval ρ = .reverted f
  | .leaf (.normal S), h => by
    simp only [normalsOnly, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact .inl ⟨S, rfl, h.1, h.2⟩
  | .leaf (.reverted f), _ => .inr ⟨f, rfl⟩
  | .leaf (.returned _ _), h => by simp [normalsOnly] at h
  | .ite _ t e, h => by
    simp only [normalsOnly, Bool.and_eq_true] at h
    simp only [Br.eval]
    split
    · exact normalsOnly_eval ρ h.2
    · exact normalsOnly_eval ρ h.1

/-- **The checked contract's constructor returns on the words `ws`**: `c?` checks, and SolidCore's
constructor on `ws` returns (it does not revert). -/
def CtorReturns (fuel : Nat) (c? : Except TypeCheck.TypeError TypeCheck.CheckedContract)
    (ws : List Nat) : Prop :=
  ∃ c, c? = .ok c ∧ ∃ d vs, Source.deployArgs? fuel ws c = some (CallResult.returned d vs)

/-- **The deployment on an argument list on which the constructor returns**, from an erasure all
of whose leaves are normal with the writes `W` and no logs, or reverts: the constructor leaves a
state with no logs whose every slot loads what `W` gives at those words. -/
theorem loadDeployed_of_normals {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br} {W : Writes}
    (herase : eraseStmt { envOf c.core with facts := argFacts wds 0 } fuel fn.body
      { initState fn with caller := .lit selfAddress } = some b)
    (hn : normalsOnly W b = true)
    {ws : List Nat} (hlen : ws.length = fn.params.length) (hargs : ∀ a ∈ ws, a < 2 ^ 256)
    (hclean : argsClean wds ws = true)
    (hret : ∃ d vs, Source.deployArgs? fuel ws c = some (CallResult.returned d vs)) :
    ∃ d, Loop.LoadDeployed fuel c ws d ∧
      ∀ k, d.loadSlot k = Writes.store ⟨ws, fun _ => 0, solHash, callerWord⟩ W k := by
  obtain ⟨ctx, r, hcons, hleaf⟩ := construct_of_erase hf hps hret0 herase hlen hargs hclean
  rcases normalsOnly_eval ⟨ws, fun _ => 0, solHash, callerWord⟩ hn with ⟨S, hS, hW, hlogs⟩ | ⟨f, hf'⟩
  · rw [hS] at hleaf
    cases r <;> simp only [LeafRel] at hleaf
    rename_i rt
    refine ⟨rt.state, ⟨⟨[], ?_⟩, ?_⟩, fun k => ?_⟩
    · rw [hcons, callBodyResult_normal hret0]
    · have := hleaf.logs
      simp only [hlogs, List.map_nil, List.map_eq_nil_iff] at this
      exact this
    · rw [← hW]
      exact loadSlot_eq rt.state S.writes _ (fun _ => rfl) hleaf.store k
  · exfalso
    rw [hf'] at hleaf
    obtain ⟨d, vs, hd⟩ := hret
    rw [hcons] at hd
    cases r <;> simp only [LeafRel] at hleaf <;> simp [FunctionDef.callBodyResult] at hd

/-- **The constructor returns where the erasure's leaf is normal.** -/
theorem returns_of_eval {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br}
    (herase : eraseStmt { envOf c.core with facts := argFacts wds 0 } fuel fn.body
      { initState fn with caller := .lit selfAddress } = some b)
    {ws : List Nat} (hlen : ws.length = fn.params.length) (hargs : ∀ a ∈ ws, a < 2 ^ 256)
    (hclean : argsClean wds ws = true) {S : SymState}
    (hS : b.eval ⟨ws, fun _ => 0, solHash, callerWord⟩ = .normal S) :
    ∃ d vs, Source.deployArgs? fuel ws c = some (CallResult.returned d vs) := by
  obtain ⟨ctx, r, hcons, hleaf⟩ := construct_of_erase hf hps hret0 herase hlen hargs hclean
  rw [hS] at hleaf
  cases r <;> simp only [LeafRel] at hleaf
  rename_i rt
  exact ⟨rt.state, [], by rw [hcons, callBodyResult_normal hret0]⟩

/-- Whether the erasure's leaf at the words `ws` is normal (the constructor returns there). -/
def normalAt (b : Br) (ws : List Nat) : Bool :=
  match b.eval ⟨ws, fun _ => 0, solHash, callerWord⟩ with
  | .normal _ => true
  | _ => false

theorem normalAt_spec {b : Br} {ws : List Nat} (h : normalAt b ws = true) :
    ∃ S, b.eval ⟨ws, fun _ => 0, solHash, callerWord⟩ = .normal S := by
  unfold normalAt at h
  split at h
  · rename_i S hS; exact ⟨S, hS⟩
  · simp at h

/-! ## What a generated module evaluates -/

/-- Whether every constructor parameter is a `uint256`-typed or `address` word, not a storage
reference. -/
def wordParams (ps : List BindingDecl) : Bool :=
  ps.all fun p => wordTy p.ty && !p.isStorageRef
where
  /-- A `uint256`-typed or `address` word. -/
  wordTy : Source.Ty → Bool
    | .uint256 => true
    | .address => true
    | _ => false

theorem wordParams_spec {ps : List BindingDecl} (h : wordParams ps = true) :
    ∀ p ∈ ps, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  revert h1
  cases p.ty <;> simp [wordParams.wordTy]

/-- Whether the constructor `fn`, with widths `wds`, erases to the tree `b`, every leaf of which is
normal with the writes `W` and no logs, or a revert. -/
def ctorLeaf (core : Contract) (fuel : Nat) (fn : FunctionDef) (wds : List Nat) (b : Br)
    (W : Writes) : Bool :=
  wordParams fn.params && fn.returns.isEmpty && widthsOf fn.params fn.paramAbiCleanups == some wds &&
    eraseStmt { envOf core with facts := argFacts wds 0 } fuel fn.body
        { initState fn with caller := .lit selfAddress } == some b && normalsOnly W b

/-- The core of the checked contract `c?`, and whether its constructor erases, with the widths
`wds`, to the tree `b` whose leaves are normal with the writes `W` and no logs, or revert; `none`
when it does not check. -/
def ctorShapeOf (fuel : Nat) (c? : Except TypeCheck.TypeError TypeCheck.CheckedContract)
    (wds : List Nat) (b : Br) (W : Writes) : Option (Contract × Bool) :=
  match c? with
  | .ok c => some (c.core,
      match TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl with
      | some fn => ctorLeaf c.core fuel fn wds b W
      | none => false)
  | .error _ => none

theorem widthsOf_length : ∀ {ps : List BindingDecl} {ks : List AbiCleanup} {wds : List Nat},
    widthsOf ps ks = some wds → wds.length = ps.length
  | [], [], _, h => by simp [widthsOf] at h; subst h; rfl
  | p :: ps, k :: ks, wds, h => by
    simp only [widthsOf, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨w, -, ws, hws, rfl⟩ := h
    simp [widthsOf_length hws]
  | [], _ :: _, _, h => by simp [widthsOf] at h
  | _ :: _, [], _, h => by simp [widthsOf] at h

/-- **The deployment for every argument list**, from one kernel evaluation of `ctorShapeOf`: the
checked core; for each list of words of the widths' count, below `2 ^ 256` and clean for the
widths, on which the constructor returns, a load-level deployment whose every cover of
`storageOf W ws` is a load cover; and the constructor returns wherever the tree's leaf is normal. -/
theorem deployed_of_ctorShapeOf {fuel : Nat}
    {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract} {wds : List Nat} {b : Br}
    {W : Writes} {core : Contract} {c : TypeCheck.CheckedContract}
    (h : ctorShapeOf fuel c? wds b W = some (core, true)) (hc : c? = .ok c) :
    c.core = core ∧
      (∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
        CtorReturns fuel c? ws →
        ∃ d, Loop.LoadDeployed fuel c ws d ∧ ∀ σ, Covers (storageOf W ws) σ → Loop.CoversLoad d σ) ∧
      (∀ ws, ws.length = wds.length → (∀ a ∈ ws, a < 2 ^ 256) → argsClean wds ws = true →
        normalAt b ws = true → CtorReturns fuel c? ws) := by
  subst hc
  obtain ⟨hk, hb⟩ := Prod.mk.inj (Option.some.inj h)
  split at hb
  case h_2 => simp at hb
  rename_i fn hf
  unfold ctorLeaf at hb
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hb
  obtain ⟨⟨⟨⟨hwp, hr⟩, hw⟩, herase⟩, hn⟩ := hb
  have hps := wordParams_spec hwp
  refine ⟨hk, fun ws hlen hargs hclean hret => ?_, fun ws hlen hargs hclean hnorm => ?_⟩
  · obtain ⟨c', hc', hret'⟩ := hret
    cases hc'
    obtain ⟨d, hd, hloads⟩ := loadDeployed_of_normals hf hps hr herase hn
      (hlen.trans (widthsOf_length hw)) hargs hclean hret'
    exact ⟨d, hd, fun σ hcov => coversLoad_of_writes hloads hcov⟩
  · obtain ⟨S, hS⟩ := normalAt_spec hnorm
    exact ⟨_, rfl, returns_of_eval hf hps hr herase (hlen.trans (widthsOf_length hw)) hargs hclean hS⟩

end SolidCore.Refinement.Generic

namespace SolidCore.Refinement.Shapes

open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar SolidCore.Solidity

/-- **The shape of a generic-stage contract deployed with argument words `ws`**: `compiled` for
`solidCoreFromArgs callerAddress fuel ws`, from a load-level deployment on `ws` whose every cover
of `s` is a load cover. -/
theorem compiledArgs {fuel mirFuel : Nat} {ws : List Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : Generic.Loop.LoadDeployed fuel c ws d)
    (hcov : ∀ σ, Generic.Covers s σ → Generic.Loop.CoversLoad d σ) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, genericValid fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCoreFromArgs callerAddress fuel ws) c code (genericValid fns s)
      (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited
    (Generic.stageAtValueArgs oracle hd hcov oracle_sourceEnvOk.ask hchk hval)
    (Generic.definedAtValueArgs hd hcov hchk hval) backend hscope ends asm hG

end SolidCore.Refinement.Shapes

/-- info: 'SolidCore.Refinement.Generic.deployed_of_ctorShapeOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.deployed_of_ctorShapeOf

/-- info: 'SolidCore.Refinement.Shapes.compiledArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.compiledArgs
