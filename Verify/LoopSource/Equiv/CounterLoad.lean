import Verify.LoopSource.Equiv.CounterCtor
import SolidCore.Refinement.Generic.CtorAll

/-!
# Counter's constructor, for every argument, at the load level (fixed context; NOT \`DeployedAtWith\`)

\`counter_load_deployed\`: for every \`n < 2 ^ 256\`, SolidCore's constructor on \`[n]\` returns a state
with no logs whose every load is \`n\` at slot 1 and 0 elsewhere. It is \`eval_stmt\` on the
constructor's body, whose function the kernel reads off the checked contract (\`ctor_eq\`), with no
enumeration of \`n\`. This is a load-level deployment fact, NOT the lifecycle statement's
\`DeployedAtWith\` (whose exact entry list stays OPEN for all \`n\`).

* \`counter_semAt_eq_runtime_all\`: for every \`n < 2 ^ 256\`, Counter deployed with \`[n]\` runs every
  \`bump(a)\` that writes every slot the deployment left nonzero as its runtime code does.
* \`cover_needed\`: the load cover is not vacuous. Deployed with \`[8]\`, \`bump(1)\` on empty storage
  succeeds under the deployed source and reverts under the runtime code.
* \`wrong_load\`: no deployment on \`[n]\` loads \`n + 1\` at slot 1.
-/

namespace Verify.LoopSource.Equiv.CounterLoad
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open SolidCore.Refinement.Generic.Loop Contracts.VerifyCounter.Source

/-- Counter's constructor, as the type checker leaves it. -/
def ctorFn : FunctionDef :=
  { name := "__constructor", selector? := none, payable := false,
    params := [{ name := "_limit", ty := .uint256, isStorageRef := false }],
    paramAbiCleanups := [.uint 256], returns := [],
    body := .block [.skip, .skip, .assign (.var "_limit") (.castOp .uintCleanup 256 (.var "_limit")),
      .block [.assign (.storage "limit") (.castOp .uintCleanup 256 (.var "_limit"))]],
    dispatchId? := none }

def ctor? : Option FunctionDef :=
  match contract? with
  | .ok c => TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl
  | .error _ => none

kernel_rfl ctor_eq ctor? (some ctorFn) using selector_eq

theorem ctor_of {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some ctorFn := by
  have h := ctor_eq; unfold ctor? at h; rw [hc] at h; exact h

/-- The constructor body's erasure: one leaf, writing the argument to slot 1. -/
def S0 : SymState := { initState ctorFn with caller := .lit selfAddress }
def Sfin : SymState :=
  { scopes := [[("_limit", .arg 0)]], writes := [(.lit 1, .arg 0)], logs := [], caller := .lit selfAddress }

theorem erase (ev : List Source.EventDecl) (tbl : FunctionTable) :
    eraseStmt { fields := vcFields, events := ev, tbl := tbl, facts := argFacts [256] 0 } fuel ctorFn.body S0 =
      some (.leaf (.normal Sfin)) := rfl

/-- **Counter's constructor on every argument**, at the load level. -/
theorem counter_load_deployed {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) :
    ∃ d, LoadDeployed fuel c [n] d ∧ ∀ k, d.loadSlot k = if k % 2 ^ 256 = 1 then n else 0 := by
  obtain ⟨hfields, hevents, -⟩ := shape_of hc
  set ρ : Val := ⟨[n], fun _ => 0, solHash, callerWord⟩ with hρ
  have hρok : ρ.Ok := fun _ => rfl
  let E : EraseEnv := { fields := c.core.storageFields, events := c.core.eventDecls, tbl := c.core.table, facts := argFacts [256] 0 }
  set ctx : Context := { Wide.ctxOf c with sender := selfAddress, value := 0, construction := true, selfDispatch? := some (ABI.selfDispatchHook fuel c.core 0) } with hctx
  have hargs : ∀ a ∈ ρ.args, a < Generic.wordSize := by simpa [hρ] using hn
  have hframe : ctorFn.initialFrame? [Value.word n] =
      some (frameOf ρ (paramLocals ctorFn.params 0 ++ ctorFn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 := bindArgs_words ρ hargs ctorFn.params 0 (by simp [ctorFn]) (by simp [ctorFn, hρ])
    simp only [FunctionDef.initialFrame?, show (ρ.args.drop 0).map Value.word = [Value.word n] from rfl] at h0 ⊢
    rw [h0]; rfl
  have hrel : StmtRel ρ E ctx
      { state := { State.empty with
          selfBalance := SolidCore.Solidity.Shared.addWord
            (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
          worldMutatedSinceAdoption := true },
        locals := [frameOf ρ (paramLocals ctorFn.params 0 ++ ctorFn.returns.map fun r => (r.name, .lit 0))] }
      S0 :=
    { fields := rfl, events := rfl, checked := rfl
      sender := rfl
      hash := rfl
      ok := hρok
      frames := rfl
      store := by
        intro k _
        simp [State.loadSlot, StorageMap.lookup?, State.empty, Writes.store, S0, initState, hρ]
      logs := by simp [State.empty, S0, initState]
      facts := argFacts_hold ρ hargs [256] 0 (by simp [argsClean, hρ]; exact hn) }
  have herase : eraseStmt E fuel ctorFn.body S0 = some (.leaf (.normal Sfin)) := by
    show eraseStmt { fields := c.core.storageFields, events := c.core.eventDecls, tbl := c.core.table, facts := argFacts [256] 0 } fuel ctorFn.body S0 = _
    rw [hfields, hevents]; exact erase _ _
  obtain ⟨r, hrun, hleaf⟩ := eval_stmt ρ E ctx fuel ctorFn.body S0 _ herase _ hrel
  cases r <;> simp only [Br.eval, LeafRel] at hleaf
  rename_i rt
  refine ⟨rt.state, ⟨⟨[], ?_⟩, ?_⟩, fun k => ?_⟩
  · have hacc : ctorFn.acceptsValue ctx.value = true := by simp [FunctionDef.acceptsValue, wordEq, hctx, ctorFn]
    show TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c) State.empty selfAddress 0
      ([n].map Value.word) = _
    simp only [TypeCheck.CheckedContract.constructWithContext?, ctor_of hc, Option.bind_eq_bind,
      Option.bind_some, List.map_cons, List.map_nil]
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, ← hctx, hacc, hframe,
      if_true, Option.map_some, Option.bind_some]
    rw [show c.core.table = E.tbl from rfl, hrun]
    rfl
  · have := hleaf.logs
    simp only [Sfin, List.map_nil, List.map_eq_nil_iff] at this
    exact this
  · rw [loadSlot_eq rt.state Sfin.writes ρ hρok hleaf.store k]
    simp only [Sfin, Writes.store, WExpr.eval, hρ, List.getD_cons_zero]
    have h1 : (1 : Nat) % Generic.wordSize = 1 := by decide
    have hW : Generic.wordSize = 2 ^ 256 := rfl
    rw [h1, hW, Nat.mod_eq_of_lt hn]
    exact if_congr ⟨Eq.symm, Eq.symm⟩ rfl rfl

/-- The deployment on \`[n]\` is the one \`counter_load_deployed\` names. -/
theorem loadDeployed_unique {fuel' : Nat} {c : TypeCheck.CheckedContract} {ws : List Nat} {d d' : Source.State}
    (h : LoadDeployed fuel' c ws d) (h' : LoadDeployed fuel' c ws d') : d = d' := by
  obtain ⟨vs, hv⟩ := h.cons
  obtain ⟨vs', hv'⟩ := h'.cons
  rw [hv] at hv'
  simp only [Option.some.injEq, CallResult.returned.injEq] at hv'
  exact hv'.1

/-- **For every \`n\`**: Counter deployed with \`[n]\` runs every load-covering \`bump(a)\` as its
runtime code does (fixed context). -/
theorem counter_semAt_eq_runtime_all {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) :
    ∃ d, LoadDeployed fuel c [n] d ∧ ∀ call, SelCallLoad bumpSel bumpFn [256] d call →
      (solidCoreFromArgs callerAddress fuel [n]).run c call = (solidCoreRuntime fuel).run c call := by
  obtain ⟨d, hd, -⟩ := counter_load_deployed hc hn
  obtain ⟨T, hT⟩ := tree_ok
  exact ⟨d, hd, fun call hv => semAt_eq_runtime_load hd (by decide) (shape_of hc).2.2 rfl rfl
    (Verify.LoopSource.MirLink.bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc) hT hv⟩

/-- **A wrong load claim is refused**: no deployment on \`[n]\` loads \`n + 1\` at slot 1. -/
theorem wrong_load {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256)
    {d : Source.State} (hd : LoadDeployed fuel c [n] d) : d.loadSlot 1 ≠ n + 1 := by
  obtain ⟨d', hd', hl⟩ := counter_load_deployed hc hn
  rw [loadDeployed_unique hd hd', hl 1]
  simp

/-- The tree's success at a valuation, computed. -/
def treeSuccess (store : Nat → Nat) : Option Bool :=
  (brTree bumpFn (argFacts [256] 0) bumpBr).map fun T => (T.eval ⟨[1], store, solHash, callerWord⟩).obs.success

theorem success_source : treeSuccess (fun k => if k % 2 ^ 256 = 1 then 8 else 0) = some true := by decide +kernel
theorem success_runtime : treeSuccess (slotValue []) = some false := by decide +kernel

/-- **The load cover is needed**: deployed with \`[8]\`, \`bump(1)\` on empty storage (which does not
write slot 1) succeeds under the deployed source and reverts under the runtime code. -/
theorem cover_needed {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) :
    (solidCoreFromArgs callerAddress fuel [8]).run c (Verify.LoopSource.MirLink.bumpCall [] 1) ≠
      (solidCoreRuntime fuel).run c (Verify.LoopSource.MirLink.bumpCall [] 1) := by
  obtain ⟨d, hd, hl⟩ := counter_load_deployed hc (n := 8) (by decide)
  obtain ⟨T, hT⟩ := tree_ok
  have hb := Verify.LoopSource.MirLink.bodyRuns_of_headline Contracts.VerifyCounter.LoopVC.body_runs_vc hc
  have hw : widthsOf bumpFn.params bumpFn.paramAbiCleanups = some [256] := rfl
  have hargs : ∀ a ∈ [1], a < 2 ^ 256 := by simp
  have hclean : argsClean [256] [1] = true := by decide
  have hdec := decode_args hw [1] rfl hargs
  rw [if_pos hclean] at hdec
  set store : Nat → Nat := fun k => if k % 2 ^ 256 = 1 then 8 else 0 with hs
  have hstore : ∀ k, (([] : List (Nat × Nat)).foldl (fun acc kv => acc.insertLoop kv.1 kv.2) d.storage)[k % 2 ^ 256]?.getD 0
      = store k := fun k => by
    simp only [List.foldl_nil]; rw [← loadSlot_eq_getD, hl k]
  have hok : ∀ k, store (k % Generic.wordSize) % Generic.wordSize = store k := fun k => by
    simp only [hs, Generic.wordSize, Nat.mod_mod]; split <;> decide
  show SolidCore.Refinement.Source.runFromArgs callerAddress fuel [8] c
      { calldata := Abi.calldata bumpSel [1], callvalue := 0, storage := [] } ≠
    runtimeRun fuel c { calldata := Abi.calldata bumpSel [1], callvalue := 0, storage := [] }
  rw [deployed_run_entry hd hstore hok (by decide) (shape_of hc).2.2 hw rfl hb hT [1] rfl hargs hclean hdec,
    runtime_run_clean (by decide) (shape_of hc).2.2 hw rfl hb hT [1] rfl hargs hclean hdec]
  intro h
  have h1 := congrArg (Option.map SolarTV.Observable.success) h
  have e1 := success_source; have e2 := success_runtime
  unfold treeSuccess at e1 e2
  rw [hT] at e1 e2
  simp only [Option.map_some, Option.some.injEq] at e1 e2 h1
  unfold fixObs at h1
  split at h1 <;> simp_all

end Verify.LoopSource.Equiv.CounterLoad

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_load_deployed

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_semAt_eq_runtime_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_semAt_eq_runtime_all

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.cover_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.cover_needed

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.wrong_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.wrong_load

/-! ## Every word: typed admission and the load-level deployment (LC's generic leaves) -/

namespace Verify.LoopSource.Equiv.CounterLoad
open SolidCore.Solidity SolidCore.Solidity.Source SolidCore.Refinement SolidCore.Refinement.Generic
open Contracts.VerifyCounter.Source

/-- **Counter's admission for every word**: `CtorAdmits` on `[n]`, `n < 2 ^ 256`, from the
constructor's shape (`ctor_of`: one non-payable `uint256` parameter, cleanup `uint 256`) by
`CtorAdmits.of_fn`. -/
theorem counter_admits_all {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) :
    CtorAdmits c Verify.LoopSource.Equiv.CounterCtor.counterInit
      (Verify.Lifecycle.initArgs Verify.LoopSource.Equiv.CounterCtor.counterInit [n]) [n] :=
  CtorAdmits.of_fn (ctor_of hc) rfl rfl (by simp [ctorFn]) (Or.inr rfl) (by simpa using hn)

/-- **Counter's load-level deployment for every word**: the constructor on `[n]` returns a state
with no logs whose every slot loads what `[(1, n)]` gives it. This is NOT `DeployedAtWith` and NOT
the bytecode's `Deploys` for every `n`. -/
theorem counter_deployedAtLoad {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) : ∃ d, DeployedAtLoad fuel c [n] [(1, n)] d := by
  obtain ⟨d, hd, hl⟩ := counter_load_deployed hc hn
  refine ⟨d, ⟨hd.cons, hd.events, fun k hk => ?_⟩⟩
  rw [hl k, Nat.mod_eq_of_lt hk]
  by_cases h : k = 1
  · subst h; rfl
  · have hb : (1 == k) = false := by simp [beq_iff_eq, Ne.symm h]
    simp [slotOf, List.find?, hb]

end Verify.LoopSource.Equiv.CounterLoad

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_admits_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_admits_all

/-- info: 'Verify.LoopSource.Equiv.CounterLoad.counter_deployedAtLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterLoad.counter_deployedAtLoad
