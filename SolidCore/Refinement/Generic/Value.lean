import SolidCore.Refinement.Generic.Stage

/-!
# The generic source stage on calls with a value

`Generic.stageAt` covers the calls of the functions of `fns` with no value. This module adds
the calls with any value `v < 2 ^ 256`: `stageAtValue` is the same stage on the scope

    fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call

where `fullScopeValue fns σ v` is `fullScope fns σ` with the call's value `v` (the same call
data, `Abi.calldata`). `stageDeployedValue` is the case of the deployed storage, and
`stageValue` the case of a constructor that leaves no storage.

Every function of the fragment is non-payable, and a call of a non-payable function with a value
other than 0 reverts with empty data:

* in SolidCore (`ABI.Contract.callCalldataAtFromWithContext?`), the dispatcher reads the
  selector, finds the function, decodes the arguments and then checks the value: a dirty argument
  word reverts with `RevertData.empty` before the value check, a clean one reaches it and
  `rejectedValueCall?` reverts with `RevertData.empty`, so both revert with empty output
  (`source_run_value`); the constructor runs with no value whatever the call's, so the call
  still runs against the deployed contract;
* in solar's module, the dispatcher checks the value first (`ne(callvalue, 0)`, then a branch to
  `revert(0, 0)`); the symbolic run `symTreeValue` runs the module with the value an unknown
  word other than 0 (`SV.paid`), which decides that branch.

`checkValue mirFuel core m fns` asks, for each function of `fns`, that SolidCore's function of
its selector is not payable and that `symTreeValue` gives a tree all of whose leaves revert
with empty output (`Tree.revertsEmpty`), so with no storage change and no logs. With `check` it
gives the stage at every value: `check` at value 0, `checkValue` at every other.

`stageAtValueEnv`, `stageDeployedValueEnv` and `stageValueEnv` are the same stages for `check` and
`checkValue` with the environment flag, under every oracle `SourceEnvOk` describes, as
`Generic.stageAtEnv` is for `stageAt`.
-/

namespace SolidCore.Refinement.Generic
open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-! ## The scope -/

/-- Every call of a function of `fns` on any argument words below `2 ^ 256`, clean or not,
with the value `v < 2 ^ 256`, from the storage `s`: `fullScope fns s` with the value `v`. -/
def fullScopeValue (fns : List Fn) (s : List (Nat × Nat)) (v : Nat) (call : Call) : Prop :=
  v < 2 ^ 256 ∧ ∃ fn ∈ fns, ∃ args : List Nat, args.length = fn.params.length ∧
    (∀ a ∈ args, a < 2 ^ 256) ∧
    call = { calldata := calldata fn.sel args, callvalue := v, storage := s }

/-- The calls with value 0 are the calls of `fullScope`. -/
theorem fullScopeValue_zero (fns : List Fn) (s : List (Nat × Nat)) (call : Call) :
    fullScopeValue fns s 0 call ↔ fullScope fns s call := by
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by decide, h⟩

/-! ## SolidCore rejects a value -/

/-- **SolidCore rejects a value**: a call with a value other than 0 of a non-payable function of
the fragment, on any argument words, reverts with empty output and leaves the storage. -/
theorem source_run_value {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {sel : Nat} (hsel : sel < 2 ^ 32)
    {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    {ws : List Nat} (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hpay : fn.payable = false) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) {v : Nat}
    (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    Source.run fuel c { calldata := Abi.calldata sel args, callvalue := v, storage := σ } =
      some (rejected σ) := by
  obtain ⟨s0, hdep⟩ := deployedStorage_of hd
  unfold Abi.deployedStorage at hdep
  dsimp only at hdep
  split at hdep
  case h_2 => simp at hdep
  rename_i deployed st hcons
  -- The constructor runs with no value, whatever the call's.
  have hcons' : TypeCheck.CheckedContract.constructWithContext? fuel c
      { c.core.context with sender := callerAddress, self := selfAddress, value := v }
      State.empty selfAddress 0 [] = some (CallResult.returned deployed st) := hcons
  -- The arguments decode, or a dirty word reverts with empty data.
  have hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word) ∨
      ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty := by
    rw [decode_args hw args hlen hargs]
    by_cases hclean : argsClean ws args = true
    · exact Or.inl (if_pos hclean)
    · exact Or.inr (if_neg hclean)
  have hvm : v % SolidCore.Solidity.Shared.wordModulus = v := Nat.mod_eq_of_lt hv
  have hacc : fn.acceptsValue v = false := by
    simp [FunctionDef.acceptsValue, hpay, wordEq, SolidCore.Solidity.Shared.norm, hvm, hv0]
  simp only [Source.run, Source.result?, hcons',
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

/-! ## The check -/

/-- Whether every leaf of the tree reverts with empty output. -/
def Tree.revertsEmpty : Tree → Bool
  | .halt ok out _ _ => !ok && out.isEmpty
  | .ite _ t e => t.revertsEmpty && e.revertsEmpty

/-- A tree whose leaves all revert with empty output gives every call a revert with empty output,
no logs and the storage before it. -/
theorem Tree.eval_revertsEmpty (ρ : Val) :
    ∀ T : Tree, T.revertsEmpty = true →
      T.eval ρ = { success := false, output := [], logs := [], store := ρ.store }
  | .halt ok out ws ls, h => by
    simp only [Tree.revertsEmpty, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .ite c t e, h => by
    simp only [Tree.revertsEmpty, Bool.and_eq_true] at h
    simp only [Tree.eval]
    split
    · exact Tree.eval_revertsEmpty ρ e h.2
    · exact Tree.eval_revertsEmpty ρ t h.1

/-- Whether a call of the function of `fns` with selector `f.sel` and a value other than 0
reverts in `m` as in SolidCore: SolidCore's function of the selector is not payable, and the
symbolic run of `m` on the selector with a value other than 0 (`symTreeValue`, `mirFuel`
blocks along each path, the environment flag `env`) reverts with empty output on every path. -/
def checkValueFn (mirFuel : Nat) (core : Contract) (m : Module) (env : EnvFlags) (f : Fn) : Bool :=
  match core.findFunctionBySelector? f.sel with
  | none => false
  | some fn =>
    !fn.payable &&
      match symTreeValue m f.sel f.params.length mirFuel env with
      | some t => t.revertsEmpty
      | none => false

/-- Whether every function of `fns` rejects a value in `m` as in SolidCore, with the environment
flag `env` (off by default). -/
def checkValue (mirFuel : Nat) (core : Contract) (m : Module) (fns : List Fn) (env : EnvFlags := .off) :
    Bool :=
  fns.all (checkValueFn mirFuel core m env)

/-! ## The stage -/

/-- The generic source stage at every value for `check` and `checkValue` with the environment flag
`env`, under every oracle when the flag is off and every oracle `SourceEnvOk` describes when it is
on. -/
theorem stageAtValueWith (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Stage (solidCore fuel) (moduleSem o) c m
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hcov, hv, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  by_cases hv0 : v = 0
  · subst hv0
    exact stageAtWith o hd henv hchk _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  have hcf := List.all_eq_true.mp hchk f hf
  have hcv := List.all_eq_true.mp hval f hf
  unfold checkFn at hcf
  unfold checkValueFn at hcv
  cases hfind : c.core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFn (envOf c.core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTreeValue m f.sel f.params.length mirFuel env with
  | none => simp [hfind, ht2] at hcv
  | some T =>
  simp only [hfind, ht1, Bool.and_eq_true, decide_eq_true_eq] at hcf
  obtain ⟨hsel, hpl, -⟩ := hcf
  simp only [hfind, ht2, Bool.and_eq_true, Bool.not_eq_true'] at hcv
  obtain ⟨hpay, hrev⟩ := hcv
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  have hsrc := source_run_value hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ
  change Source.run fuel c _ = some obs at hrun
  rw [hsrc] at hrun
  cases hrun
  have hc0 := callFacts f.sel hsel args hargs σ
  have hcfv : CallFactsAt .paid f.sel args.length ⟨args, slotValue σ, solHash⟩
      { calldata := Abi.calldata f.sel args, callvalue := v, storage := σ } :=
    { value := by
        show BitVec.ofNat 256 v ≠ 0
        intro h
        apply hv0
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
        simpa using this
      size := hc0.size
      args := hc0.args
      selector := hc0.selector
      store := hc0.store
      ok := hc0.ok }
  rw [← hlen] at ht2
  rw [symTreeValue_sound hcfv o m (henv.envAsk _ _) ht2, Tree.eval_revertsEmpty _ _ hrev]
  rfl

/-- **The generic source stage at every value**: a checked contract whose constructor leaves the
storage entries `s` and no logs and a lowered MIR module that `check` and `checkValue` accept give
the stage from SolidCore to the module's lowered MIR semantics, under every oracle, on every call
of a function of `fns` on any argument words below `2 ^ 256`, with any value below `2 ^ 256`, from
any storage that writes every slot of `s`. -/
theorem stageAtValue (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true)
    (hval : checkValue mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) :=
  stageAtValueWith o hd (env := .off) SourceAsk.off hchk hval

/-- The generic source stage at every value from the deployed storage `s`. -/
theorem stageDeployedValue (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true)
    (hval : checkValue mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ v, fullScopeValue fns s v call) :=
  SolarTV.Stage.mono (stageAtValue o hd hchk hval) fun _ ⟨v, h⟩ =>
    ⟨s, v, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage at every value for a contract whose constructor leaves no storage,
from any storage. -/
theorem stageValue (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns = true)
    (hval : checkValue mirFuel c.core m fns = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ v, fullScopeValue fns σ v call) :=
  SolarTV.Stage.mono (stageAtValue o hd hchk hval) fun _ ⟨σ, v, h⟩ =>
    ⟨σ, v, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- **The generic source stage at every value with the environment flag**: `stageAtValue` for a
module that `check ... true` and `checkValue ... true` accept, under every oracle `SourceEnvOk`
describes. -/
theorem stageAtValueEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns .all = true)
    (hval : checkValue mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) :=
  stageAtValueWith o hd henv.ask hchk hval

/-- The generic source stage at every value with the environment flag from the deployed storage
`s`. -/
theorem stageDeployedValueEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} (hchk : check fuel mirFuel c.core m fns .all = true)
    (hval : checkValue mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ v, fullScopeValue fns s v call) :=
  SolarTV.Stage.mono (stageAtValueEnv o henv hd hchk hval) fun _ ⟨v, h⟩ =>
    ⟨s, v, fun kv hkv => ⟨kv, hkv, rfl⟩, h⟩

/-- The generic source stage at every value with the environment flag for a contract whose
constructor leaves no storage, from any storage. -/
theorem stageValueEnv (o : Oracle) (henv : SourceEnvOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns .all = true)
    (hval : checkValue mirFuel c.core m fns .all = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ v, fullScopeValue fns σ v call) :=
  SolarTV.Stage.mono (stageAtValueEnv o henv hd hchk hval) fun _ ⟨σ, v, h⟩ =>
    ⟨σ, v, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

/-- The caller-only stage at every value for a contract whose constructor leaves no storage, from
any storage, under every oracle with SolidCore's caller. -/
theorem stageValueCaller (o : Oracle) (henv : CallerOk o) {fuel mirFuel : Nat}
    {c : TypeCheck.CheckedContract} {d : Source.State}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d []) {m : Module}
    {fns : List Fn} (hchk : check fuel mirFuel c.core m fns .callerOnly = true)
    (hval : checkValue mirFuel c.core m fns .callerOnly = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ v, fullScopeValue fns σ v call) :=
  SolarTV.Stage.mono (stageAtValueWith o hd henv.ask hchk hval) fun _ ⟨σ, v, h⟩ =>
    ⟨σ, v, fun _ hkv => absurd hkv List.not_mem_nil, h⟩

end SolidCore.Refinement.Generic
