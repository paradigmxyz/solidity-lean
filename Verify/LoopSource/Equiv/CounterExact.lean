import Verify.LoopSource.Equiv.CounterLoad
import Verify.LoopSource.Equiv.CounterSame
import Verify.Lifecycle.Symbolic

/-!
# Counter's lifecycle statement for every constructor argument

`CounterLoad.counter_load_deployed` gives, for every `n < 2 ^ 256`, the loads of the state Counter's
constructor leaves, which do not fix the entry list of its storage hash map. This module gives the
exact state and the bytecode half, so the lifecycle statement holds for every argument word:

* `eval_assignVar_exact`, `eval_assignStorage_exact`: the results of a local and a storage-field
  assignment in the erasure's fragment, as runtimes (the steps of `eval_stmt`, with the result
  named instead of related);
* `counter_deployedAtWith_all`: for every `n < 2 ^ 256`, SolidCore's constructor on `[n]` leaves
  exactly the storage entries `[(1, n)]` and no logs (`DeployedAtWith`);
* `counter_deploys_all`: for every `n < 2 ^ 256`, EthLib runs solar's init code for Counter with
  the encoded `n` to success, returns `CounterSame.runtime` and leaves storage `[(1, n)]`, from one
  kernel evaluation of the symbolic creation frame (`Creation.Sym.symCheck`);
* `counter_lifecycle_all`: the two together, `Verify.Lifecycle.Statement` for every `n < 2 ^ 256`;
* `deployedAtLoad_of`: `DeployedAtWith` gives the load-level `DeployedAtLoad` that
  `Source.run_of_load` consumes, and `counter_deployedAtLoad_all` is its instance;
* `wrong_slot`, `wrong_value`, `wrong_load`, `deploys_wrong`: a wrong slot or value is refused, for
  the exact source state (`[(0, n)]`, `[(1, n + 1)]`), its loads and the bytecode's storage.

Bounds: the argument is one word, `n < 2 ^ 256`; the creation frame is the one
`SolidCore.Refinement.Deploy` fixes (no value, no address derivation or code deposit).
-/

namespace Verify.LoopSource.Equiv.CounterExact

open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-! ## Two statements of the fragment, with their results named -/

/-- A local assignment in the fragment leaves the runtime with the erasure's scopes. -/
theorem eval_assignVar_exact {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) (m : Nat) {x : String} {e : Expr} {gs : List WExpr} {v : WExpr}
    {L' : Scopes} (he : eraseExpr E.fields S e = some (gs, v)) (hL : Scopes.set S.scopes x v = some L')
    (hg : gs.any (fun g => g.eval ρ != 0) = false) (htg : S.tags = [] := by rfl) :
    Stmt.eval (m + 1) E.tbl ctx rt (.assign (.var x) e) =
      .done (.ok (.normal { rt with locals := L'.map (frameOf ρ) })) := by
  obtain ⟨old, hold⟩ := Scopes.get?_of_set hL
  have hx : rt.lookupLocal? x = some (.word (old.eval ρ)) :=
    hrel.expr.locals x old (by simp [SymState.word?, htg, hold])
  have hmem : rt.lookupMemoryRef? x = none := by simp [Runtime.lookupMemoryRef?, hx]
  have hbase : rt.lookupStorageBase? x = none := by simp [Runtime.lookupStorageBase?, hx]
  have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
  have hres : LValue.resolveWithRuntime (.var x) ctx rt = .done (.ok (.local x, rt)) := by
    simp [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr,
      Expr.resolveLValueFuel, hbase, hx]
    rfl
  have hassign : rt.assignLocal? x (.word (v.eval ρ)) =
      some { rt with locals := L'.map (frameOf ρ) } := by
    have := assignLocal_word hrel.frames (x := x) (by simp [htg]) hL
    rwa [htg, frameOfT_nil] at this
  rw [Stmt.eval]
  simp only [LValue.wantsMemoryRefRhs, hmem, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, heval, caught_exprResult, hg]
  split
  · split
    · simp_all
    · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign,
        ResolvedLValue.asStoragePath?]
      rfl
  · simp only [bind_done_ok, hres, caught_done_ok, ite_self, ResolvedLValue.write, hassign,
      ResolvedLValue.asStoragePath?]
    rfl

/-- A storage-field assignment in the fragment writes the field's slot and changes nothing else. -/
theorem eval_assignStorage_exact {ρ : Val} {E : EraseEnv} {ctx : Context} {rt : Runtime} {S : SymState}
    (hrel : StmtRel ρ E ctx rt S) (m : Nat) {x : String} {e : Expr} {k off bytes : Nat}
    {gs : List WExpr} {v : WExpr} (hk : fieldOf? E.fields x = some (k, off, bytes))
    (he : eraseExpr E.fields S e = some (gs, v)) (hg : gs.any (fun g => g.eval ρ != 0) = false) :
    Stmt.eval (m + 1) E.tbl ctx rt (.assign (.storage x) e) =
      .done (.ok (.normal { rt with
        state := rt.state.storeSlot k (fieldWrite (rt.state.loadSlot k) (v.eval ρ) off bytes) })) := by
  obtain ⟨f, hfx, rfl, rfl, rfl⟩ := fieldOf?_spec hrel.fields hk
  have heval := eval_eq ρ E.fields ctx rt S hrel.expr he
  have hres : LValue.resolveWithRuntime (.storage x) ctx rt =
      .done (.ok (.storageField x, rt)) := by
    simp [LValue.resolveWithRuntime, Expr.resolveLValue, LValue.toExpr, Expr.resolveLValueFuel]
    rfl
  have hw := v.eval_lt ρ
  have hsl : rt.state.loadSlot f.slot = (S.writes.read (.lit f.slot)).eval ρ :=
    slot_read hrel.expr hfx.slot
  have hslw : rt.state.loadSlot f.slot < wordSize := hsl ▸ WExpr.eval_lt _ _
  rw [Stmt.eval]
  simp only [LValue.wantsMemoryRefRhs, Bool.false_eq_true, ↓reduceIte, heval, caught_exprResult, hg]
  simp only [bind_done_ok, hres, caught_done_ok, ResolvedLValue.write,
    store_field hfx hslw _ hw, ite_self]
  rfl

/-- The storage a single write of a word to slot 1 of the empty state leaves: exactly one entry. -/
theorem toList_insert_empty (k v : Nat) :
    (Std.HashMap.insert (∅ : Std.HashMap Nat Nat) k v).toList = [(k, v)] := by
  simpa using Std.HashMap.toList_insert_perm (m := (∅ : Std.HashMap Nat Nat)) (k := k) (v := v)

/-! ## Counter's constructor: the exact state -/

open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic.Loop
open Contracts.VerifyCounter.Source Verify.LoopSource.Equiv.CounterLoad

theorem storage_single {st : State} (hst : st.storage = {}) (n : Nat) (hn : n < 2 ^ 256) :
    (st.storeSlot 1 n).storage.toList = [(1, n)] := by
  simp only [State.storeSlot, StorageMap.insertLoop, hst]
  rw [show SolidCore.Solidity.Shared.norm 1 = 1 from rfl,
    show SolidCore.Solidity.Shared.norm n = n from Nat.mod_eq_of_lt hn]
  exact toList_insert_empty 1 n

/-- **Counter's constructor on every argument leaves exactly `[(1, n)]`**: for every `n < 2 ^ 256`,
SolidCore's constructor of Counter on `[n]` returns, with no logs, a state whose storage entry list
is exactly `[(1, n)]`. -/
theorem counter_deployedAtWith_all {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) :
    ∃ d, Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n)] := by
  obtain ⟨hfields, hevents, -⟩ := shape_of hc
  set ρ : Val := ⟨[n], fun _ => 0, solHash, callerWord⟩ with hρ
  have hρok : ρ.Ok := fun _ => rfl
  let E : EraseEnv := { fields := c.core.storageFields, events := c.core.eventDecls, tbl := c.core.table, facts := argFacts [2 ^ 256 - 1] 0 }
  set ctx : Context := { Wide.ctxOf c with sender := selfAddress, value := 0, construction := true, selfDispatch? := some (ABI.selfDispatchHook fuel c.core 0) } with hctx
  have hargs : ∀ a ∈ ρ.args, a < Generic.wordSize := by simpa [hρ] using hn
  have hframe : ctorFn.initialFrame? [Value.word n] =
      some (frameOf ρ (paramLocals ctorFn.params 0 ++ ctorFn.returns.map fun r => (r.name, .lit 0))) := by
    have h0 := bindArgs_words ρ hargs ctorFn.params 0 (by simp [ctorFn]) (by simp [ctorFn, hρ])
    simp only [FunctionDef.initialFrame?, show (ρ.args.drop 0).map Value.word = [Value.word n] from rfl] at h0 ⊢
    rw [h0]; rfl
  set st0 : State := { State.empty with
      selfBalance := SolidCore.Solidity.Shared.addWord
        (SolidCore.Solidity.Shared.Account.balanceAt ctx.accountBalances ctx.self) ctx.value
      worldMutatedSinceAdoption := true } with hst0
  set rt0 : Runtime :=
    { state := st0,
      locals := [frameOf ρ (paramLocals ctorFn.params 0 ++ ctorFn.returns.map fun r => (r.name, .lit 0))] }
    with hrt0
  have hrel : StmtRel ρ E ctx rt0 CounterLoad.S0 :=
    { fields := rfl, events := rfl, checked := rfl
      sender := rfl
      hash := rfl
      ok := hρok
      frames := rfl
      store := by
        intro k _
        simp [State.loadSlot, StorageMap.lookup?, State.empty, Writes.store, CounterLoad.S0, initState, hρ, hrt0, hst0]
      logs := by simp [State.empty, CounterLoad.S0, initState, hrt0, hst0]
      facts := argFacts_hold ρ hargs [2 ^ 256 - 1] 0 (by simp [argsClean, hρ]; exact Nat.le_of_lt_succ hn) }
  have hE : E.fields = vcFields := hfields
  -- the statements of the body, one by one
  have hrel1 := hrel.pushScope
  have he1 : eraseExpr E.fields CounterLoad.S0.push (.castOp .uintCleanup 256 (.var "_limit")) = some ([], .arg 0) := by
    rw [hE]; rfl
  have hL : Scopes.set CounterLoad.S0.push.scopes "_limit" (.arg 0) = some [[], [("_limit", .arg 0)]] := rfl
  have hrel2 : StmtRel ρ E ctx { rt0.pushScope with locals := ([[], [("_limit", .arg 0)]] : Scopes).map (frameOf ρ) }
      { CounterLoad.S0.push with scopes := [[], [("_limit", .arg 0)]] } := { hrel1 with frames := rfl }
  have he2 : eraseExpr E.fields { CounterLoad.S0.push with scopes := [[], [("_limit", .arg 0)]] }.push
      (.castOp .uintCleanup 256 (.var "_limit")) = some ([], .arg 0) := by
    rw [hE]; rfl
  have hk : fieldOf? E.fields "limit" = some (1, 0, 32) := by rw [hE]; rfl
  have key : ∀ m, Stmt.eval (m + 1 + 1 + 1) E.tbl ctx rt0 ctorFn.body = .done (.ok (.normal
      { rt0 with state := st0.storeSlot 1 (fieldWrite (st0.loadSlot 1) ((WExpr.arg 0).eval ρ) 0 32) })) := by
    intro m
    have hskip : ∀ rt, Stmt.eval (m + 1 + 1) E.tbl ctx rt .skip = .done (.ok (.normal rt)) := fun _ => by
      rw [Stmt.eval]; rfl
    exact eval_block_of ((evalList_cons_normal (hskip _)).trans <| (evalList_cons_normal (hskip _)).trans <|
      (evalList_cons_normal (eval_assignVar_exact hrel1 (m + 1) he1 hL rfl)).trans <|
      (evalList_cons_normal (eval_block_of ((evalList_cons_normal
        (eval_assignStorage_exact hrel2.pushScope m hk he2 rfl)).trans (evalList_nil _ _ _ _)))).trans
      (evalList_nil _ _ _ _))

  have hrun := key (fuel - 3)
  rw [show fuel - 3 + 1 + 1 + 1 = fuel from by unfold fuel; omega] at hrun
  have hval : fieldWrite (st0.loadSlot 1) ((WExpr.arg 0).eval ρ) 0 32 = n := by
    simp [fieldWrite, WExpr.eval, hρ]; exact hn
  refine ⟨st0.storeSlot 1 (fieldWrite (st0.loadSlot 1) ((WExpr.arg 0).eval ρ) 0 32), ⟨[], ?_⟩, ?_, rfl⟩
  · show TypeCheck.CheckedContract.constructWithContext? fuel c (Wide.ctxOf c) State.empty selfAddress 0
      ([n].map Value.word) = _
    simp only [TypeCheck.CheckedContract.constructWithContext?, ctor_of hc, Option.bind_eq_bind,
      Option.bind_some, List.map_cons, List.map_nil]
    simp only [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry, ← hctx, hframe]
    rw [show c.core.table = E.tbl from rfl, hrun]
    rfl
  · rw [hval]
    exact storage_single rfl n hn


/-- Two runs of one constructor that both return leave the same state. -/
private theorem returned_eq {x : Option CallResult} {d d' : Source.State}
    (h : ∃ vs, x = some (.returned d vs)) (h' : ∃ vs, x = some (.returned d' vs)) : d = d' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, h'⟩ := h'
  cases h'
  rfl

/-- Every `DeployedAtWith` of Counter on `[n]` names the storage `[(1, n)]`. -/
theorem deployedAtWith_unique {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) {d : Source.State} {s : List (Nat × Nat)}
    (hd : Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d s) : s = [(1, n)] := by
  obtain ⟨d', hd'⟩ := counter_deployedAtWith_all hc hn
  rw [← hd.storage, returned_eq hd.cons hd'.cons, hd'.storage]

/-- **A wrong slot is refused**: no deployment of Counter on `[n]` leaves exactly `[(0, n)]`. -/
theorem wrong_slot {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256)
    (d : Source.State) :
    ¬ Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(0, n)] := fun hd => by
  simpa using deployedAtWith_unique hc hn hd

/-- **A wrong value is refused**: no deployment of Counter on `[n]` leaves exactly `[(1, n + 1)]`. -/
theorem wrong_value {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256)
    (d : Source.State) :
    ¬ Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n + 1)] := fun hd => by
  simpa using deployedAtWith_unique hc hn hd

/-! ## The load-level consequence -/

/-- **The exact deployment gives the load-level one** that `Source.run_of_load` consumes. -/
theorem deployedAtLoad_of {fuel' : Nat} {c : TypeCheck.CheckedContract} {ws : List Nat} {d : Source.State}
    {s : List (Nat × Nat)} (hd : Verify.Lifecycle.DeployedAtWith fuel' c (Verify.Lifecycle.wordArgs ws) d s) :
    DeployedAtLoad fuel' c ws s d := by
  obtain ⟨hl, hloads, -⟩ := loadDeployed_of hd
  exact ⟨hl.cons, hl.events, fun k hk => by rw [hloads k, Nat.mod_eq_of_lt hk]; rfl⟩

/-- **Counter's load-level deployment for every word, from the exact one.** -/
theorem counter_deployedAtLoad_all {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) : ∃ d, Verify.Lifecycle.DeployedAtWith fuel c (Verify.Lifecycle.wordArgs [n]) d [(1, n)] ∧
      DeployedAtLoad fuel c [n] [(1, n)] d := by
  obtain ⟨d, hd⟩ := counter_deployedAtWith_all hc hn
  exact ⟨d, hd, deployedAtLoad_of hd⟩

/-- **A wrong load is refused**: no load-level deployment of Counter on `[n]` gives slot 1 the
value `n + 1`, nor, when `n ≠ 0`, slot 0 the value `n`. -/
theorem wrong_load {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat} (hn : n < 2 ^ 256)
    (d : Source.State) :
    ¬ DeployedAtLoad fuel c [n] [(1, n + 1)] d ∧ (n ≠ 0 → ¬ DeployedAtLoad fuel c [n] [(0, n)] d) := by
  obtain ⟨d', -, hl'⟩ := counter_deployedAtLoad_all hc hn
  have same : ∀ {s} k, k < 2 ^ 256 → DeployedAtLoad fuel c [n] s d → slotOf s k = slotOf [(1, n)] k :=
    fun k hk h => by rw [← h.loads k hk, returned_eq h.cons hl'.cons, hl'.loads k hk]
  refine ⟨fun h => ?_, fun h0 h => ?_⟩
  · have e := same 1 (by decide) h
    simp [slotOf] at e
  · have e := same 0 (by decide) h
    simp [slotOf] at e
    exact h0 e

/-! ## The bytecode half for every argument -/

section Bytecode
open Verify.Lifecycle.Creation.Sym

set_option maxRecDepth 100000 in
/-- One kernel evaluation of the symbolic creation frame on solar's init code for Counter with one
argument word: no path condition, the returned code is `CounterSame.runtime` with no argument byte
in it, and the one storage write is the argument word at slot 1. -/
theorem counter_symCheck : symCheck 4096 CounterCtor.counterInit 1 []
    (patched CounterSame.runtime []) [(1, .arg 0)] = true := by decide +kernel

/-- **The bytecode deploys Counter for every argument word**: for every `n < 2 ^ 256`, EthLib runs
solar's init code for Counter with the encoded `n` appended to success, returns
`CounterSame.runtime` and leaves the storage `[(1, n)]`. -/
theorem counter_deploys_all {n : Nat} (hn : n < 2 ^ 256) :
    Deploys (Verify.Lifecycle.initArgs CounterCtor.counterInit [n]) CounterSame.runtime [(1, n)] := by
  have h := deploys_all counter_symCheck [BitVec.ofNat 256 n] rfl (by simp)
  have e1 : [BitVec.ofNat 256 n].map BitVec.toNat = [n] := by
    simp only [List.map_cons, List.map_nil, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have e2 : storeOf [BitVec.ofNat 256 n] [(1, .arg 0)] = [(1, n)] := by
    simp only [storeOf, E.eval, List.map_cons, List.map_nil, List.getD_cons_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn]
  rw [e1, e2, codeOf_patched, List.foldl_nil] at h
  exact h

/-- **A wrong bytecode storage claim is refused**: the creation on `[n]` does not leave
`[(1, n + 1)]`, nor, when `n ≠ 0`, `[(0, n)]`. -/
theorem deploys_wrong {n : Nat} (hn : n < 2 ^ 256) :
    ¬ Deploys (Verify.Lifecycle.initArgs CounterCtor.counterInit [n]) CounterSame.runtime [(1, n + 1)] ∧
      (n ≠ 0 → ¬ Deploys (Verify.Lifecycle.initArgs CounterCtor.counterInit [n]) CounterSame.runtime [(0, n)]) := by
  obtain ⟨o, ho, -, -, hs⟩ := counter_deploys_all hn
  have same : ∀ {s}, Deploys (Verify.Lifecycle.initArgs CounterCtor.counterInit [n]) CounterSame.runtime s →
      ∀ k, SolarTV.slotValue s k = SolarTV.slotValue [(1, n)] k := fun h k => by
    obtain ⟨o', ho', -, -, hs'⟩ := h
    rw [ho] at ho'
    cases ho'
    rw [← hs', hs]
  refine ⟨fun h => ?_, fun h0 h => ?_⟩
  · have e := same h 1
    simp only [SolarTV.slotValue, List.foldl_cons, List.foldl_nil] at e
    simp only [ite_true, Nat.mod_eq_of_lt hn] at e
    by_cases hl : n + 1 < 2 ^ 256
    · rw [Nat.mod_eq_of_lt hl] at e; omega
    · rw [show n + 1 = 2 ^ 256 by omega, Nat.mod_self] at e; omega
  · have e := same h 1
    simp only [SolarTV.slotValue, List.foldl_cons, List.foldl_nil, Nat.mod_eq_of_lt hn] at e
    simp at e
    exact h0 (by omega)

end Bytecode

/-! ## The lifecycle statement for every argument -/

/-- **Counter's lifecycle statement for every argument word**: for every `n < 2 ^ 256`, solar's init
code for Counter with the encoded `n` deploys `CounterSame.runtime` with storage `[(1, n)]`, and
SolidCore's constructor on `[n]` leaves exactly `[(1, n)]` and no logs. -/
theorem counter_lifecycle_all {c : TypeCheck.CheckedContract} (hc : contract? = .ok c) {n : Nat}
    (hn : n < 2 ^ 256) :
    Verify.Lifecycle.Statement fuel c CounterCtor.counterInit CounterSame.runtime [n] [(1, n)] :=
  ⟨counter_deploys_all hn, counter_deployedAtWith_all hc hn⟩

end Verify.LoopSource.Equiv.CounterExact

/-- info: 'Verify.LoopSource.Equiv.CounterExact.eval_assignVar_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.eval_assignVar_exact

/-- info: 'Verify.LoopSource.Equiv.CounterExact.eval_assignStorage_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.eval_assignStorage_exact

/-- info: 'Verify.LoopSource.Equiv.CounterExact.toList_insert_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.toList_insert_empty

/-- info: 'Verify.LoopSource.Equiv.CounterExact.counter_deployedAtWith_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.counter_deployedAtWith_all

/-- info: 'Verify.LoopSource.Equiv.CounterExact.deployedAtWith_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.deployedAtWith_unique

/-- info: 'Verify.LoopSource.Equiv.CounterExact.wrong_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.wrong_slot

/-- info: 'Verify.LoopSource.Equiv.CounterExact.wrong_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.wrong_value

/-- info: 'Verify.LoopSource.Equiv.CounterExact.deployedAtLoad_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.deployedAtLoad_of

/-- info: 'Verify.LoopSource.Equiv.CounterExact.counter_deployedAtLoad_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.counter_deployedAtLoad_all

/-- info: 'Verify.LoopSource.Equiv.CounterExact.wrong_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.wrong_load

/-- info: 'Verify.LoopSource.Equiv.CounterExact.counter_symCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.counter_symCheck

/-- info: 'Verify.LoopSource.Equiv.CounterExact.counter_deploys_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.counter_deploys_all

/-- info: 'Verify.LoopSource.Equiv.CounterExact.deploys_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.deploys_wrong

/-- info: 'Verify.LoopSource.Equiv.CounterExact.counter_lifecycle_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verify.LoopSource.Equiv.CounterExact.counter_lifecycle_all
