import Verify.ShapeGeneric
import SolidCore.Refinement.Generic.LoopRun
import SolidCore.Refinement.Generic.Value

/-!
# The certified shape of a loop-free contract's runtime code, with no constructor

`Shapes.compiled` and `Shapes.compiled0` state the generic route's `Compiled` against
`solidCore fuel`, which first runs the constructor (`Wide.DeployedAt`) and then the call from
the deployed storage overwritten by the call's. A contract whose constructor the generic
creation frame does not evaluate (a loop in the constructor, in a function or modifier only the
constructor reaches, or in a state variable's initializer; base constructor arguments) has no
`DeployedAt` there, so nothing about its calls could be stated.

This module states the same shape against `Generic.Loop.solidCoreRuntime fuel`, SolidCore's ABI
dispatcher on the runtime code alone, from the state whose storage is the call's: the semantics
the loop route already uses, and the one the runtime bytecode's own run (`Target.run`, from the
call's storage) has. Deployment is outside the statement: it says nothing about what the
constructor writes, and it needs no constructor at all. Its valid calls are every call of a
function of `fns` on any argument words, from **any** storage (no `Covers` premise), so on the
runtime code it covers at least every call `compiled0` covers.

* `runtime_run_rejected`, `runtime_run_erased`: `source_run`'s two cases for
  `runtimeRun`, with no `DeployedAt`: a dirty argument word reverts with empty data; a clean
  call runs as the erased tree (`LoopRun.runtime_run_clean` of `bodyRuns_of_erase`).
* `runtime_run_value`: a call with a value other than 0 of a non-payable function reverts with
  empty data and the call's storage.
* `stageRuntimeWith`, `definedRuntime`, `stageRuntimeValueWith`, `definedRuntimeValue`: the
  generic source stage and its totality from `Generic.check` (and `Generic.checkValue`).
* `compiled0Runtime`, `compiledRuntime`: `Shapes.compiled_of` on those stages.

Every theorem is proved; no axiom is added.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Generic

/-- **A dirty argument word reverts on the runtime code**, with empty data and the call's storage. -/
theorem runtime_run_rejected {fuel : Nat} {c : TypeCheck.CheckedContract} {sel : Nat}
    (hsel : sel < 2 ^ 32) {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    (args : List Nat) (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .error .empty)
    (σ : List (Nat × Nat)) :
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (Abi.rejected σ) := by
  simp only [runtimeRun, runtimeResult?, ABI.Contract.callCalldataAtFromWithContext?,
    Dirty.bytes_calldata, Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length], hdec]
  simp only [ABI.Contract.revertedCall?, ABI.Contract.encodeRevertData?, bind, Option.bind,
    Option.map_some, Source.observe, Abi.rejected]
  simp

/-- **A call of a function of the generic source stage (typed parameters and returns included) with clean
argument words runs on the runtime code as the tree of its body's leaves**: `Loop.runtime_run_clean`
with the typed decode (`abi_clean` on `widthsOfT` and `tagsOk`). -/
theorem runtime_run_cleanT {fuel : Nat} {c : TypeCheck.CheckedContract} {σ : List (Nat × Nat)}
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
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold runtimeRun runtimeResult?
  simp only [Dirty.bytes_calldata]
  exact And.right (abi_clean hsel hfind hw hret fuel _ callerAddress (getD_storage_empty σ) rfl
    (.lit callerWord) hlen hargs (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0
      (by simpa using hclean)) rfl htags hdec hT (fun rt hrel => hb _ _ rt hrel) _ rfl)

/-- **SolidCore's runtime code runs a call of a function of the fragment as its erased tree**,
from any storage `σ`, on any argument words below `2 ^ 256`, clean or dirty. -/
theorem runtime_run_erased {fuel : Nat} {c : TypeCheck.CheckedContract} {σ : List (Nat × Nat)}
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFn (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
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
    exact runtime_run_cleanT hsel hfind hw hret htags (bodyRuns_of_erase hb) ht args hlen hargs hclean hdec
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [runtime_run_rejected hsel hfind args hdec σ]
    rfl

/-- **The runtime code rejects a value**: a call with a value other than 0 of a non-payable
function of the fragment, on any argument words, reverts with empty output and the call's
storage. -/
theorem runtime_run_value {fuel : Nat} {c : TypeCheck.CheckedContract} {sel : Nat}
    (hsel : sel < 2 ^ 32) {fn : FunctionDef} (hfind : c.core.findFunctionBySelector? sel = some fn)
    {ws : List Nat} (hw : widthsOfT fn.params fn.paramAbiCleanups = some ws)
    (hpay : fn.payable = false) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) {v : Nat}
    (hv0 : v ≠ 0) (hv : v < 2 ^ 256) (σ : List (Nat × Nat)) :
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := v, storage := σ } =
      some (rejected σ) := by
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
  simp only [runtimeRun, runtimeResult?, ABI.Contract.callCalldataAtFromWithContext?,
    Dirty.bytes_calldata, Dirty.readSelector_calldata _ hsel, hfind]
  rw [show ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]]
  rcases hdec with hdec | hdec <;> rw [hdec] <;>
    simp only [hacc, Bool.false_eq_true, ↓reduceIte, ABI.Contract.rejectedValueCall?,
      ABI.Contract.revertedEmptyCall?, ABI.Contract.revertedCall?,
      ABI.Contract.encodeRevertData?, bind, Option.bind, Option.map_some, Source.observe,
      rejected]

/-- **The generic source stage on the runtime code**, from any storage, with no constructor. -/
theorem stageRuntimeWith (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true) :
    Stage (solidCoreRuntime fuel) (moduleSem o) c m (fun call => ∃ σ, fullScope fns σ call) := by
  rintro _ ⟨σ, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, ht2, hcf⟩ := check_mem hchk hf
  change runtimeRun fuel c _ = some obs at hrun
  rw [runtime_run_erased hsel hfind ht1 args (by rw [hlen, hpl]) hargs] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTree_sound (callFacts f.sel hsel args hargs σ) o m (henv.envAsk _ _) ht2,
    ← Tree.eval_of_agree hcf]

/-- SolidCore's runtime code finishes every call of the scope `check` accepts. -/
theorem definedRuntime {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true) :
    Defined (solidCoreRuntime fuel) c (fun call => ∃ σ, fullScope fns σ call) := by
  rintro _ ⟨σ, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, -, -⟩ := check_mem hchk hf
  change (runtimeRun fuel c _).isSome = true
  rw [runtime_run_erased hsel hfind ht1 args (by rw [hlen, hpl]) hargs]
  rfl

/-- **The generic source stage on the runtime code at every value**, from any storage. -/
theorem stageRuntimeValueWith (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Stage (solidCoreRuntime fuel) (moduleSem o) c m
      (fun call => ∃ σ v, fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hv, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  by_cases hv0 : v = 0
  · subst hv0
    exact stageRuntimeWith o henv hchk _ ⟨σ, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := check_mem hchk hf
  obtain ⟨hpay, T, ht2, hrev⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  change runtimeRun fuel c _ = some obs at hrun
  rw [runtime_run_value hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTreeValue_sound (callFactsFromValue f.sel hsel args hargs σ callerWord hv0 hv) o m
    (henv.envAsk _ _) ht2, Tree.eval_revertsEmpty _ _ hrev]
  rfl

/-- SolidCore's runtime code finishes every call of the scope at every value. -/
theorem definedRuntimeValue {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : check fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Defined (solidCoreRuntime fuel) c (fun call => ∃ σ v, fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hv, f, hf, args, hlen, hargs, rfl⟩
  by_cases hv0 : v = 0
  · subst hv0
    exact definedRuntime hchk _ ⟨σ, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := check_mem hchk hf
  obtain ⟨hpay, -, -, -⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFn_widths ht1
  change (runtimeRun fuel c _).isSome = true
  rw [runtime_run_value hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ]
  rfl

end SolidCore.Refinement.Generic.Loop

namespace SolidCore.Refinement.Shapes
open SolarTV SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Solar
open SolidCore.Solidity SolidCore.Refinement.Generic.Loop

/-- The valid calls of the runtime route without a value: a function of `fns` on any argument
words below `2 ^ 256`, no value, from any storage. -/
def runtimeValid0 (fns : List Fn) (call : Call) : Prop :=
  ∃ σ, fullScope fns σ call

/-- The valid calls of the runtime route: a function of `fns` on any argument words below
`2 ^ 256`, any value below `2 ^ 256`, from any storage. -/
def runtimeValid (fns : List Fn) (call : Call) : Prop :=
  ∃ σ v, Generic.fullScopeValue fns σ v call

/-- **The shape of a loop-free contract's runtime code on calls without a value**: the generic
check, the backend stages, the final EVM IR's fuel and the loop checker, with no constructor. -/
theorem compiled0Runtime {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, runtimeValid0 fns call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, runtimeValid0 fns call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCoreRuntime fuel) c code (runtimeValid0 fns)
      (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited (stageRuntimeWith oracle oracle_sourceEnvOk.ask hchk)
    (definedRuntime hchk) backend hscope ends asm hG

/-- **The shape of a loop-free contract's runtime code at every value**, with no constructor. -/
theorem compiledRuntime {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {m : MIR.Lowered.Module} {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.check fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, runtimeValid fns call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, runtimeValid fns call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCoreRuntime fuel) c code (runtimeValid fns)
      (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited (stageRuntimeValueWith oracle oracle_sourceEnvOk.ask hchk hval)
    (definedRuntimeValue hchk hval) backend hscope ends asm hG

/-- A call of every runtime scope without a value: the first function on zero words, from the
empty storage. -/
theorem runtimeValid0_inhabited (f : Fn) (fns : List Fn) :
    ∃ call, runtimeValid0 (f :: fns) call :=
  ⟨_, [], f, List.mem_cons_self, List.replicate f.params.length 0, List.length_replicate,
    fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide, rfl⟩

/-- A call of every runtime scope: the first function on zero words, no value, from the empty
storage. -/
theorem runtimeValid_inhabited (f : Fn) (fns : List Fn) :
    ∃ call, runtimeValid (f :: fns) call :=
  ⟨_, [], 0, by decide, f, List.mem_cons_self, List.replicate f.params.length 0,
    List.length_replicate, fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide, rfl⟩

end SolidCore.Refinement.Shapes

/-- info: 'SolidCore.Refinement.Shapes.compiled0Runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.compiled0Runtime

/-- info: 'SolidCore.Refinement.Shapes.compiledRuntime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.compiledRuntime
