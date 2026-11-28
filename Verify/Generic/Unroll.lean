import Verify.LoopSource.Proof.EraseLoopCall
import Verify.ShapeGeneric

/-!
# The generic source stage with unrolled loops

The generic source check (`Generic.check`, `Stage.lean`) erases each external function's body with
`eraseStmt`, which has no loop. A function whose loops run a number of iterations its own words
fix (a `for` loop to a literal limit, a modifier's loop to a literal argument, nested ones) is
inside the generic stage once its body is erased with `Loop.eraseLoopCall`
(`Verify/LoopSource/Proof/EraseLoopCall.lean`): every loop whose condition is a closed word at every
iteration is unrolled, one iteration per iteration of SolidCore's `Stmt.evalFor`, at most
`Loop.unrollBudget` iterations, and its guards, reverts and returns stay in the tree. Nothing about
the loop is assumed or summarised: the unrolled tree is the body's run (`runs_eraseLoopCall`), and
the symbolic run of the lowered MIR (`symTree`, which folds the words its branches read) must agree
with it in canonical form, as for a loop-free body.

* `eraseFnL`, `checkFnL`, `checkL`: `eraseFn`, `checkFn` and `check` with `eraseLoopCall` in place
  of `eraseStmt`, the trees compared by `Tree.agreeAC` (`Tree.agree`, or `agree` once every sum is
  written in one order, `WExpr.ac`); `checkL_mem` is `check_mem`.
* `source_runL`: SolidCore runs a call as its `eraseFnL` tree, `source_run`'s statement, whose proof
  is `source_run`'s with `runs_eraseLoopCall` as the body's run (`abi_clean`'s premise).
* `stageAtWithL`, `definedAtL`, `stageAtValueWithL`, `definedAtValueL`: the stage and its totality,
  as `stageAtWith`, `definedAt`, `stageAtValueWith` and `definedAtValue` state them.
* `Shapes.compiledL`, `Shapes.compiled0L`: `Shapes.compiled` and `compiled0` from `checkL`, with
  the same conclusion word for word, so a published statement does not change with the route.

A loop outside the unrolled shape (a condition that reads an argument or storage, more than
`unrollBudget` iterations, a `break` or `continue`, a `while` or `do`-`while` loop) leaves
`eraseLoopCall` `none`, so `checkL` is `false`: such a function stays refused. The backend stages
and the assembly checker are the generic route's: the bytecode still loops, through cut points, and
the gas bound is the loop checker's at the final EVM IR's fixed fuel (certify.py's `Runs/Ends.lean`).
-/

namespace SolidCore.Refinement.Generic
open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-- The erasure of an external call of `fn` with its loops unrolled: `eraseFn` with
`Loop.eraseLoopCall` in place of `eraseStmt`. -/
def eraseFnL (E : EraseEnv) (fuel : Nat) (fn : FunctionDef) : Option Tree :=
  match widthsOfT fn.params fn.paramAbiCleanups with
  | none => none
  | some ws =>
    if fn.returns.all wordBinding && tagsOk fn then do
      let b ← Loop.eraseLoopCall { E with facts := argFacts ws 0 } fuel fn.body (initState fn)
      let t ← brTree fn (argFacts ws 0) b
      some (paramGuards ws 0 t)
    else none

/-- The parameter widths of a function the unrolled erasure accepts. -/
theorem eraseFnL_widths {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {T : Tree}
    (h : eraseFnL E fuel fn = some T) : ∃ ws, widthsOfT fn.params fn.paramAbiCleanups = some ws := by
  unfold eraseFnL at h
  split at h
  · simp at h
  · rename_i ws hw
    exact ⟨ws, hw⟩

/-- **SolidCore runs a call of a function as its unrolled erased tree**: `source_run`'s statement for
`eraseFnL`, from any storage `σ` that writes every slot the constructor's entries `s` write, on any
argument words below `2 ^ 256`, clean or dirty. -/
theorem source_runL {fuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {σ : List (Nat × Nat)}
    (hcov : Covers s σ) {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {T : Tree}
    (hT : eraseFnL (envOf c.core) fuel fn = some T) (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256) :
    Source.run fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } =
      some (T.eval ⟨args, slotValue σ, solHash, callerWord⟩).obs := by
  unfold eraseFnL at hT
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
    rw [Wide.callAt_of_args sel args hargs σ, Wide.run_eq_at hd, Wide.map_ofNat_toNat args hargs]
    exact (abi_clean hsel hfind hw hret fuel _ callerAddress
      (st0 := { d with storage := σ.foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage })
      (getD_storage_cover hd hcov) hd.events
      (.lit callerWord) hlen hargs (argFacts_hold _ hargs ws 0 (by simpa using hclean)) rfl htags
      hdec ht (fun rt hrel => Loop.runs_eraseLoopCall _ _ fuel fn.body _ b hb _ rt hrel) _ rfl).2
  · rw [if_neg hclean]
    rw [if_neg hclean] at hdec
    rw [run_rejected hd hsel hfind args hdec σ]
    rfl

/-! ## Sums in one order

An unrolled loop folds its counter into the words it computes, and the two sides spell the same sum
in different orders: the source adds a literal last (`x + 1`, then `(x + 1) + 2`), solar's lowered MIR
first (`1 + x`, `2 + (1 + x)`). `WExpr.ac` writes every sum as its non-literal terms, in order, then
one literal (their sum modulo `2 ^ 256`), and `Tree.agreeAC` accepts two trees whose forms so written
agree (`Tree.agree`). Nothing else is reordered, so two sums whose non-literal terms come in other
orders still differ. `WExpr.eval_ac`: the form has the word's value. -/

/-- The non-literal terms of a sum, in order, and the sum of its literals. -/
def WExpr.addTerms : WExpr → List WExpr × Nat
  | .bin .add a b => (a.addTerms.1 ++ b.addTerms.1, a.addTerms.2 + b.addTerms.2)
  | .lit n => ([], n)
  | e => ([e], 0)

/-- The terms added up, right-nested. -/
def WExpr.sumOf : List WExpr → WExpr
  | [] => .lit 0
  | [t] => t
  | t :: ts => .bin .add t (WExpr.sumOf ts)

/-- A sum of terms and a literal: the terms, then the literal unless it is 0. -/
def WExpr.ofTerms (ts : List WExpr) (c : Nat) : WExpr :=
  if c % wordSize = 0 then WExpr.sumOf ts
  else if ts = [] then .lit (c % wordSize) else .bin .add (WExpr.sumOf ts) (.lit (c % wordSize))

/-- Every sum in one order: its non-literal terms, then its literal. -/
def WExpr.ac : WExpr → WExpr
  | .bin .add a b => WExpr.ofTerms (WExpr.bin .add a.ac b.ac).addTerms.1 (WExpr.bin .add a.ac b.ac).addTerms.2
  | .bin op a b => .bin op a.ac b.ac
  | .un op a => .un op a.ac
  | .sinit k => .sinit k.ac
  | .sel c a b => .sel c.ac a.ac b.ac
  | .hash a b => .hash a.ac b.ac
  | e => e

theorem WExpr.eval_addTerms (ρ : Val) : ∀ e : WExpr,
    e.eval ρ = ((e.addTerms.1.map (·.eval ρ)).sum + e.addTerms.2) % wordSize
  | .bin .add a b => by
    have ha := WExpr.eval_addTerms ρ a
    have hb := WExpr.eval_addTerms ρ b
    simp only [WExpr.addTerms, List.map_append, List.sum_append, WExpr.eval, BinOp.eval]
    rw [ha, hb]
    simp only [Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]
    congr 1
    omega
  | .lit n => by simp [WExpr.addTerms, WExpr.eval]
  | .arg i => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)]
  | .init k => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)]
  | .un op a => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ (.un op a))]
  | .bin .sub a b | .bin .mul a b | .bin .div a b | .bin .lt a b | .bin .gt a b | .bin .eq a b
  | .bin .and a b | .bin .or a b | .bin .xor a b | .bin .shl a b | .bin .shr a b
  | .bin .byte a b => by
    simp only [WExpr.addTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero]
    exact (Nat.mod_eq_of_lt (WExpr.eval_lt ρ _)).symm
  | .sinit k => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ (.sinit k))]
  | .sel c a b => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ (.sel c a b))]
  | .hash a b => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ (.hash a b))]
  | .caller => by simp [WExpr.addTerms, Nat.mod_eq_of_lt (WExpr.eval_lt ρ .caller)]

theorem WExpr.eval_sumOf (ρ : Val) : ∀ ts : List WExpr,
    (WExpr.sumOf ts).eval ρ = (ts.map (·.eval ρ)).sum % wordSize
  | [] => by simp [WExpr.sumOf, WExpr.eval]
  | [t] => by simp [WExpr.sumOf, Nat.mod_eq_of_lt (WExpr.eval_lt ρ t)]
  | t :: u :: ts => by
    have ih := WExpr.eval_sumOf ρ (u :: ts)
    simp only [WExpr.sumOf] at ih ⊢
    simp only [WExpr.eval, BinOp.eval, ih, List.map_cons, List.sum_cons, Nat.mod_mod,
      Nat.add_mod_mod, Nat.mod_add_mod]

theorem WExpr.eval_ofTerms (ρ : Val) (ts : List WExpr) (c : Nat) :
    (WExpr.ofTerms ts c).eval ρ = ((ts.map (·.eval ρ)).sum + c) % wordSize := by
  unfold WExpr.ofTerms
  split
  · rename_i hc
    rw [WExpr.eval_sumOf, Nat.add_mod, hc, Nat.add_zero, Nat.mod_mod]
  · split
    · subst ts
      simp [WExpr.eval]
    · simp only [WExpr.eval, BinOp.eval, WExpr.eval_sumOf, Nat.mod_mod, Nat.add_mod_mod,
        Nat.mod_add_mod]

theorem WExpr.eval_ac (ρ : Val) : ∀ e : WExpr, e.ac.eval ρ = e.eval ρ
  | .bin .add a b => by
    simp only [WExpr.ac]
    rw [WExpr.eval_ofTerms, ← WExpr.eval_addTerms]
    simp only [WExpr.eval, BinOp.eval, WExpr.eval_ac ρ a, WExpr.eval_ac ρ b]
  | .bin .sub a b | .bin .mul a b | .bin .div a b | .bin .lt a b | .bin .gt a b | .bin .eq a b
  | .bin .and a b | .bin .or a b | .bin .xor a b | .bin .shl a b | .bin .shr a b
  | .bin .byte a b => by
    simp only [WExpr.ac, WExpr.eval, WExpr.eval_ac ρ a, WExpr.eval_ac ρ b]
  | .un op a => by simp only [WExpr.ac, WExpr.eval, WExpr.eval_ac ρ a]
  | .sinit k => by simp only [WExpr.ac, WExpr.eval, WExpr.eval_ac ρ k]
  | .sel c a b => by simp only [WExpr.ac, WExpr.eval, WExpr.eval_ac ρ c, WExpr.eval_ac ρ a,
      WExpr.eval_ac ρ b]
  | .hash a b => by simp only [WExpr.ac, WExpr.eval, WExpr.eval_ac ρ a, WExpr.eval_ac ρ b]
  | .lit _ | .arg _ | .init _ | .caller => rfl

/-- A byte of output, its word's sums in one order. -/
def OByte.ac : OByte → OByte
  | .lit b => .lit b
  | .byteOf e i => .byteOf e.ac i

theorem OByte.eval_ac (ρ : Val) (b : OByte) : b.ac.eval ρ = b.eval ρ := by
  cases b <;> simp [OByte.ac, OByte.eval, WExpr.eval_ac]

/-- Every word of a tree, its sums in one order. -/
def Tree.ac : Tree → Tree
  | .halt ok out ws ls =>
    .halt ok (out.map OByte.ac) (ws.mapW WExpr.ac) (ls.map (Log.mapL WExpr.ac OByte.ac))
  | .ite c t e => .ite c.ac t.ac e.ac

theorem Tree.eval_ac (ρ : Val) : ∀ T : Tree, T.ac.eval ρ = T.eval ρ
  | .halt ok out ws ls => by
    simp only [Tree.ac, Tree.eval, List.map_map, Writes.store_mapW ρ _ (WExpr.eval_ac ρ)]
    congr 2
    · funext b
      exact OByte.eval_ac ρ b
    · congr 1
      funext l
      exact Log.eval_mapL ρ _ _ (WExpr.eval_ac ρ) (OByte.eval_ac ρ) l
  | .ite c t e => by
    simp only [Tree.ac, Tree.eval, WExpr.eval_ac, Tree.eval_ac ρ t, Tree.eval_ac ρ e]

/-- Two trees agree (`Tree.agree`), or agree once every sum is written in one order. -/
def Tree.agreeAC (t1 t2 : Tree) : Bool := Tree.agree t1 t2 || Tree.agree t1.ac t2.ac

/-- **Trees that agree with their sums in one order are equal on every call.** -/
theorem Tree.eval_of_agreeAC {t1 t2 : Tree} (h : Tree.agreeAC t1 t2 = true) (ρ : Val) :
    t1.eval ρ = t2.eval ρ := by
  unfold Tree.agreeAC at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Tree.eval_of_agree h ρ
  · rw [← Tree.eval_ac ρ t1, Tree.eval_of_agree h ρ, Tree.eval_ac]

/-- Whether the function of `fns` with selector `f.sel` lowers to `m` with its loops unrolled:
`checkFn` with `eraseFnL`. -/
def checkFnL (fuel mirFuel : Nat) (core : Contract) (m : Module) (env : EnvFlags) (f : Fn) : Bool :=
  decide (f.sel < 2 ^ 32) &&
    match core.findFunctionBySelector? f.sel with
    | none => false
    | some fn =>
      decide (fn.params.length = f.params.length) &&
        match eraseFnL (envOf core) fuel fn, symTree m f.sel f.params.length mirFuel env with
        | some t1, some t2 => Tree.agreeAC t1 t2
        | _, _ => false

/-- Whether every function of `fns` lowers to `m` with its loops unrolled. -/
def checkL (fuel mirFuel : Nat) (core : Contract) (m : Module) (fns : List Fn)
    (env : EnvFlags := .off) : Bool :=
  fns.all (checkFnL fuel mirFuel core m env)

/-- What `checkL` accepts of a function of `fns`, as `check_mem`. -/
theorem checkL_mem {fuel mirFuel : Nat} {core : Contract} {m : Module} {fns : List Fn}
    {env : EnvFlags} (hchk : checkL fuel mirFuel core m fns env = true) {f : Fn} (hf : f ∈ fns) :
    f.sel < 2 ^ 32 ∧ ∃ fn t1 t2, core.findFunctionBySelector? f.sel = some fn ∧
      fn.params.length = f.params.length ∧ eraseFnL (envOf core) fuel fn = some t1 ∧
      symTree m f.sel f.params.length mirFuel env = some t2 ∧ Tree.agreeAC t1 t2 = true := by
  have hcf := List.all_eq_true.mp hchk f hf
  unfold checkFnL at hcf
  cases hfind : core.findFunctionBySelector? f.sel with
  | none => simp [hfind] at hcf
  | some fn =>
  cases ht1 : eraseFnL (envOf core) fuel fn with
  | none => simp [hfind, ht1] at hcf
  | some t1 =>
  cases ht2 : symTree m f.sel f.params.length mirFuel env with
  | none => simp [hfind, ht1, ht2] at hcf
  | some t2 =>
  simp only [hfind, ht1, ht2, Bool.and_eq_true, decide_eq_true_eq] at hcf
  exact ⟨hcf.1, fn, t1, t2, rfl, hcf.2.1, ht1, rfl, hcf.2.2⟩

/-- **The generic source stage with unrolled loops**, as `stageAtWith`. -/
theorem stageAtWithL (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : checkL fuel mirFuel c.core m fns env = true) :
    Stage (solidCore fuel) (moduleSem o) c m (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, ht2, hcf⟩ := checkL_mem hchk hf
  change Source.run fuel c _ = some obs at hrun
  rw [source_runL hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTree_sound (callFacts f.sel hsel args hargs σ) o m (henv.envAsk _ _) ht2,
    ← Tree.eval_of_agreeAC hcf]

/-- SolidCore finishes every call of the stage's scope that `checkL` accepts, as `definedAt`. -/
theorem definedAtL {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : checkL fuel mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ, Covers s σ ∧ fullScope fns σ call) := by
  rintro _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, t2, hfind, hpl, ht1, -, -⟩ := checkL_mem hchk hf
  have hsrc := source_runL hd hcov hsel hfind ht1 args (by rw [hlen, hpl]) hargs
  change (Source.run fuel c _).isSome = true
  rw [hsrc]
  rfl

/-- **The generic source stage with unrolled loops at every value**, as `stageAtValueWith`. -/
theorem stageAtValueWithL (o : Oracle) {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract}
    {d : Source.State} {s : List (Nat × Nat)}
    (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s)
    {m : Module} {fns : List Fn} {env : EnvFlags} (henv : SourceAsk env o)
    (hchk : checkL fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Stage (solidCore fuel) (moduleSem o) c m
      (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hcov, hv, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  by_cases hv0 : v = 0
  · subst hv0
    exact stageAtWithL o hd henv hchk _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩ obs hrun
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := checkL_mem hchk hf
  obtain ⟨hpay, T, ht2, hrev⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFnL_widths ht1
  change Source.run fuel c _ = some obs at hrun
  rw [source_run_value hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ] at hrun
  cases hrun
  rw [← hlen] at ht2
  rw [symTreeValue_sound (callFactsFromValue f.sel hsel args hargs σ callerWord hv0 hv) o m
    (henv.envAsk _ _) ht2, Tree.eval_revertsEmpty _ _ hrev]
  rfl

/-- SolidCore finishes every call at every value that `checkL` and `checkValue` accept, as
`definedAtValue`. -/
theorem definedAtValueL {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : SolidCore.Refinement.Wide.DeployedAt fuel c d s) {m : Module}
    {fns : List Fn} {env : EnvFlags} (hchk : checkL fuel mirFuel c.core m fns env = true)
    (hval : checkValue mirFuel c.core m fns env = true) :
    Defined (solidCore fuel) c (fun call => ∃ σ v, Covers s σ ∧ fullScopeValue fns σ v call) := by
  rintro _ ⟨σ, v, hcov, hv, f, hf, args, hlen, hargs, rfl⟩
  by_cases hv0 : v = 0
  · subst hv0
    exact definedAtL hd hchk _ ⟨σ, hcov, f, hf, args, hlen, hargs, rfl⟩
  obtain ⟨hsel, fn, t1, -, hfind, hpl, ht1, -⟩ := checkL_mem hchk hf
  obtain ⟨hpay, -⟩ := checkValue_mem hval hf hfind
  obtain ⟨ws, hw⟩ := eraseFnL_widths ht1
  have hsrc := source_run_value hd hsel hfind hw hpay args (by rw [hlen, hpl]) hargs hv0 hv σ
  change (Source.run fuel c _).isSome = true
  rw [hsrc]
  rfl

end SolidCore.Refinement.Generic

namespace SolidCore.Refinement.Shapes
open SolarTV SolidCore.Refinement SolidCore.Refinement.Final SolidCore.Refinement.Abi
open SolidCore.Refinement.Solar SolidCore.Solidity

/-- **The shape of a generic-stage contract with unrolled loops**: `compiled`'s conclusion, from
`checkL` in place of `check`. -/
theorem compiledL {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.checkL fuel mirFuel c.core m fns env = true)
    (hval : Generic.checkValue mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, genericValid fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited
    (Generic.stageAtValueWithL oracle hd oracle_sourceEnvOk.ask hchk hval)
    (Generic.definedAtValueL hd hchk hval) backend hscope ends asm hG

/-- **The shape of a generic-stage contract with unrolled loops on calls without a value**:
`compiled0`'s conclusion, from `checkL`. -/
theorem compiled0L {fuel mirFuel : Nat} {c : TypeCheck.CheckedContract} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Wide.DeployedAt fuel c d s) {m : MIR.Lowered.Module}
    {fns : List Fn} {env : Generic.EnvFlags}
    (hchk : Generic.checkL fuel mirFuel c.core m fns env = true)
    {q : Assemble.Program} {code : ByteArray} {scope : Call → Prop} {cert : Assemble.Cert}
    {mx : List Nat} {N : Nat}
    (inhabited : ∃ call, genericValid0 fns s call)
    (backend : Stage (mirSem oracle) (evmirSem oracle) m q scope)
    (hscope : ∀ call, genericValid0 fns s call → scope call)
    (ends : ∀ call, (EVM.Program.run oracle q call N).isSome = true)
    (asm : AssembleLoop.checkL q code cert mx = true)
    (hG : AssembleLoop.gasBoundL cert N < 2 ^ 64) :
    Compiled (solidCore fuel) c code (genericValid0 fns s) (fun _ => AssembleLoop.gasBoundL cert N) :=
  compiled_of inhabited (Generic.stageAtWithL oracle hd oracle_sourceEnvOk.ask hchk)
    (Generic.definedAtL hd hchk) backend hscope ends asm hG

end SolidCore.Refinement.Shapes

/-- info: 'SolidCore.Refinement.Generic.source_runL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.source_runL

/-- info: 'SolidCore.Refinement.Shapes.compiledL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.compiledL

/-- info: 'SolidCore.Refinement.Shapes.compiled0L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Shapes.compiled0L
