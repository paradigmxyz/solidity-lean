import SolidCore.Refinement.Generic.StageFrom
import SolidCore.Refinement.SourceOracle

/-!
# The generic source stage in every world

`stageInAtWith` is the generic source stage (`Generic.stageAtWith`) with SolidCore run in a world
`W` (`solidCoreIn W`, SolidCore/Refinement/SourceOracle.lean): any call oracle and any other accounts'
code. A function the erasure accepts makes no external call, so its body's interaction tree is a
finished one (`eval_stmt` gives `.done` in every context, the other accounts' code included) and
every call oracle folds it to the same result; SolidCore then runs the call as the erased tree in
every world (`source_runIn`), and the stage holds for every world and every MIR oracle, with no
hypothesis on either (in particular no `CallsAgree`). So the call-free functions of a contract that
calls out elsewhere (a pair's `getReserves`, a token's `approve`) get their stage in the open world that
`Verify/SourceOracle.lean`'s `holds_of_runs` asks of the lowering, `stageIn_runs`.
-/

namespace SolidCore.Refinement.Generic
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-- The context of a call in the world `W`: the deployed context with `W`'s account code. -/
def ctxIn (W : World) (c : TypeCheck.CheckedContract) : Source.Context :=
  { Wide.ctxOf c with accountCodes := W.codes.getD c.core.context.accountCodes }

/-- A finished interaction tree folds to its result under every call oracle. -/
theorem callAns_done {ans : Ans} {fuel : Nat} {table : FunctionTable} {context : Context}
    {fn : FunctionDef} {st : Source.State} {args : List Value} {r : CallResult}
    (h : fn.call fuel table context st args = some (.done (.ok r))) :
    Source.callAns ans fuel table context fn st args = some r := by
  simp only [Source.callAns, h, Option.bind_some]
  rfl

/-- `Source.runIn W` of a call from the storage `σ`, once the constructor's result is known. -/
theorem runIn_eq_at (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) (sel : Nat) (ws : List EthLib.Base.U256)
    (σ : List (Nat × Nat)) :
    Source.runIn W fuel c (Wide.callAt sel ws σ) =
      Option.map (Source.observe (Wide.callAt sel ws σ))
        (Source.ABI.Oracle.callCalldata W.ans fuel c.core (ctxIn W c)
          { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage }
          selfAddress callerAddress 0
          ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes (ws.map (·.toNat)))) := by
  obtain ⟨vs, hc⟩ := hd.cons
  simp only [Source.runIn, Source.resultIn?, show (Wide.callAt sel ws σ).callvalue = 0 from rfl,
    show (Wide.callAt sel ws σ).storage = σ from rfl,
    show (Wide.callAt sel ws σ).calldata = Abi.calldata sel (ws.map (·.toNat)) from rfl]
  rw [show ({ c.core.context with sender := callerAddress, self := selfAddress, value := 0 } :
    Source.Context) = Wide.ctxOf c from rfl, hc]
  simp only [Dirty.bytes_calldata]
  rfl

/-- SolidCore in every world rejects dirty argument words as `Source.run` does. -/
theorem runIn_rejected (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn) (args : List Nat)
    (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty)
    (σ : List (Nat × Nat)) :
    Source.runIn W fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) := by
  rw [Wide.callAt_of_args sel args hargs σ, runIn_eq_at W hd, Wide.map_ofNat_toNat args hargs]
  simp only [Source.ABI.Oracle.callCalldata, Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length], hdec]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, Abi.rejected]
  simp [Wide.callAt]

/-- The oracle's dispatcher calls a function whose body is a finished interaction tree as the
closed dispatcher does. -/
theorem callCalldata_done (ans : Ans) {fuel : Nat} {core : Contract} {base : Source.Context}
    {st0 : Source.State} {a : Nat} {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : core.findFunctionBySelector? sel = some fn) {args : List Nat}
    {vals : List Value}
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok vals) {R : CallResult}
    (h : fn.call fuel core.table (ABI.Contract.callContextAtWithBase core base selfAddress a 0
      ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)) st0 vals =
      some (.done (.ok R))) :
    Source.ABI.Oracle.callCalldata ans fuel core base st0 selfAddress a 0
        ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) =
      ABI.Contract.callCalldataAtFromWithContext? fuel core base st0 selfAddress a 0
        ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args) := by
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [Source.ABI.Oracle.callCalldata, ABI.Contract.callCalldataAtFromWithContext?,
    Dirty.readSelector_calldata _ hsel, hfind, hdrop, hdec, callAns_done (ans := ans) h,
    FunctionDef.call?, h]
  rfl

/-- SolidCore in the world `W` runs a call of a function of the fragment on clean argument words as
its body's tree. -/
theorem source_runIn_clean (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true) (htags : tagsOk fn = true) {b : Br}
    (hb : eraseStmt { envOf c.core with facts := argFacts ws 0 } fuel fn.body (initState fn) = some b)
    {T : Tree} (hT : brTree fn (argFacts ws 0) b = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) =
      .ok (tyVals (fn.params.map BindingDecl.ty) args)) :
    Source.runIn W fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  rw [SolidCore.Refinement.Wide.callAt_of_args sel args hargs σ,
    runIn_eq_at W hd, SolidCore.Refinement.Wide.map_ofNat_toNat args hargs]
  obtain ⟨⟨R, hR⟩, hobs⟩ := abi_clean hsel hfind hw hret fuel (ctxIn W c) callerAddress
    (st0 := { d with storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) d.storage })
    (getD_storage_cover hd hcov) hd.events (.lit callerWord) hlen hargs
    (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)) rfl htags
    hdec hT (fun rt hrel => eval_stmt _ _ _ fuel fn.body _ b hb rt hrel)
    (Wide.callAt sel (args.map (BitVec.ofNat 256)) σ) rfl
  rw [callCalldata_done W.ans hsel hfind hdec ((call_tyVals hw hlen hargs _ _ _ _).trans hR)]
  exact hobs

/-- **SolidCore runs a call of a function of the fragment as its erased tree, in every world**, from any storage
`σ` that writes every slot the constructor's entries `s` write, on any argument words below
`2 ^ 256`, clean or dirty. -/
theorem source_runIn (W : World) {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.runIn W fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
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
    exact source_runIn_clean W hd hcov hsel hfind hw hret htags hb ht args hlen hargs hclean hdec
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [runIn_rejected W hd hsel hfind args hargs hdec σ]
    rfl

/-! ## The stage in every world -/

/-- The generic source stage for `check` with the environment flag `env`, under every oracle when
the flag is off and every oracle `SourceEnvOk` describes when it is on. -/
theorem stageInAtWith (W : World) (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, ht2, hcf⟩ := check_mem hchk hf
  change Source.runIn W fuel c _ = some obs at hrun
  rw [source_runIn W hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTree_sound (callFacts f.sel hsel args hargs σ) o m (henv.envAsk _ _) ht2,
    ← Tree.eval_of_agree hcf]

/-- **The generic source stage**: a checked contract whose constructor leaves the storage entries
`s` and no logs and a lowered MIR module that `check` accepts give the stage from SolidCore in every world `W` to the
module's lowered MIR semantics, under every oracle, on every call of a function of `fns` on any
argument words below `2 ^ 256`, with no value, from any storage that writes every slot of `s`. -/
theorem stageInAt (W : World) (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageInAtWith W o hd (env := .off) SourceAsk.off hchk

/-- The generic source stage from the deployed storage `s`. -/
theorem stageInDeployed (W : World) (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fullScope fns s) :=
  SolarTV.Stage.mono (stageInAt W o hd hchk) fun _ h => ⟨s, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage for a contract whose constructor leaves no storage, from any
storage. -/
theorem stageIn (W : World) (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageInAt W o hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- **The generic source stage with the environment flag**: `stageAt` for a module that
`check ... true` accepts, which may read the caller and hash two words, under every oracle whose
caller is `callerWord` and whose Keccak-256 of two words is `solHash` (`SourceEnvOk`). -/
theorem stageInAtEnv (W : World) (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageInAtWith W o hd henv.ask hchk

/-- The generic source stage with the environment flag from the deployed storage `s`. -/
theorem stageInDeployedEnv (W : World) (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fullScope fns s) :=
  SolarTV.Stage.mono (stageInAtEnv W o henv hd hchk) fun _ h => ⟨s, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage with the environment flag for a contract whose constructor leaves no
storage, from any storage. -/
theorem stageInEnv (W : World) (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .all = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageInAtEnv W o henv hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- The generic source stage with the caller-only flags (a contract that reads `msg.sender` but
hashes nothing), from any storage that writes every slot of `s`, under every oracle with
SolidCore's caller. -/
theorem stageInAtCaller (W : World) (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .callerOnly = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) :=
  stageInAtWith W o hd henv.ask hchk

/-- The caller-only stage for a contract whose constructor leaves no storage, from any storage. -/
theorem stageInCaller (W : World) (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module} {fns : List Fn}
    (hchk : check fuel mirFuel c.core m fns .callerOnly = true) :
    Stage (solidCoreIn W fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) :=
  SolarTV.Stage.mono (stageInAtCaller W o henv hd hchk) fun _ ⟨σ, h⟩ =>
    ⟨σ, fun _ hkv => absurd hkv List.not_mem_nil, h⟩


/-- **The lowering of `holds_of_runs`, for the call-free functions of a contract**: the generic stage
in every world, for every oracle that agrees with it (and every other). -/
theorem stageIn_runs {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true) :
    ∀ o W, CallsAgree o W →
      Stage (solidCoreIn W fuel) (moduleSem o) c m (fullScope fns s) :=
  fun o W _ => stageInDeployed W o hd hchk

/-- info: 'SolidCore.Refinement.Generic.stageInAtWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageInAtWith

/-- info: 'SolidCore.Refinement.Generic.stageIn_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageIn_runs

/-! ## The same run in every world -/

/-- **A function the check accepts runs the same in every world**: on every call of the check's
scope, SolidCore in the world `W` shows what `Source.run` shows. -/
theorem runIn_eq_run (W : World) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags}
    (hchk : check fuel mirFuel c.core m fns env = true) :
    ∀ call, (∃ σ, Covers s σ ∧ fullScope fns σ call) →
      Source.runIn W fuel c call = Source.run fuel c call := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := check_mem hchk hf
  rw [source_runIn W hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs,
    source_run hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs]

/-- info: 'SolidCore.Refinement.Generic.runIn_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runIn_eq_run

end SolidCore.Refinement.Generic
