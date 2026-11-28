import SolidCore.Refinement.Generic.LoopRun

/-!
# Loops that end at no fuel, and calls whose body fails

The converse of the ranking certificates of `Loop.lean`, strong enough to reach a call's
result. `evalFor_never` says a loop without progress never finishes normally; a call's result
needs more, since the dispatcher folds the body's interaction tree: these lemmas say the run
**fails** (`.done (.error e)`, out of fuel among them), at every fuel.

* `evalFor_err`: a `for` loop whose condition holds from every runtime of `P`, and whose body and
  update, at every fuel, either fail or come back to `P`, fails at every fuel.
* `forLoop_err`, `evalList_cons_err`, `eval_block_err`: the failure through the `for` statement,
  statement lists and blocks.
* `runtime_run_err`: a call of a function with clean argument words whose body fails, from every
  runtime related to its first symbolic state, has no result in `runtimeRun`: no fuel ends it.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source
open EvmCompiler.Simulation (Interaction)

/-- What a body or an update does at a fuel: it fails, or it finishes normally in `Q`. -/
def ErrOr (t : SolI Result) (Q : Runtime → Prop) : Prop :=
  (∃ e, t = .done (.error e)) ∨ ∃ rt, t = .done (.ok (.normal rt)) ∧ Q rt

/-- **A `for` loop without progress fails at every fuel.** -/
theorem evalFor_err {tbl : FunctionTable} {ctx : Context} {cond : Expr} {post body : Stmt}
    (P : Runtime → Prop)
    (h : ∀ rt, P rt → ∃ w rt', (Expr.eval ctx rt cond).caught = .done (.ok (.ok (.word w, rt'))) ∧
      wordTruthy w = true ∧ ∀ f, ErrOr (Stmt.eval f tbl ctx rt' body) fun rb =>
        ErrOr (Stmt.eval f tbl ctx rb post) P) :
    ∀ fuel rt, P rt → ∃ e, Stmt.evalFor fuel tbl ctx rt cond post body = .done (.error e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro rt _
    refine ⟨SolidityFailure.outOfFuel, ?_⟩
    first | rfl | (simp only [Stmt.evalFor]; done) | (simp only [Stmt.evalFor]; rfl)
  | succ f ih =>
    intro rt hp
    obtain ⟨w, rt', hc, ht, hb⟩ := h rt hp
    simp only [Stmt.evalFor]
    rw [hc, bind_done_ok]
    simp only [Value.expectWord, wordTruthy_norm, ht, ite_true]
    rcases hb f with ⟨e, he⟩ | ⟨rb, hb1, hpost⟩
    · rw [he]; exact ⟨e, rfl⟩
    · rw [hb1, bind_done_ok]
      dsimp only
      rcases hpost with ⟨e, he⟩ | ⟨rp, hp1, hP⟩
      · rw [he]; exact ⟨e, rfl⟩
      · rw [hp1, bind_done_ok]
        dsimp only
        exact ih rp hP

/-- **The `for` statement of a loop without progress fails at every fuel.** -/
theorem forLoop_err {tbl : FunctionTable} {ctx : Context} {init : Stmt} {cond : Expr}
    {post body : Stmt} (P : Runtime → Prop)
    (h : ∀ rt, P rt → ∃ w rt', (Expr.eval ctx rt cond).caught = .done (.ok (.ok (.word w, rt'))) ∧
      wordTruthy w = true ∧ ∀ f, ErrOr (Stmt.eval f tbl ctx rt' body) fun rb =>
        ErrOr (Stmt.eval f tbl ctx rb post) P)
    {rt : Runtime} (hinit : ∀ f, ErrOr (Stmt.eval f tbl ctx rt.pushScope init) P) :
    ∀ fuel, ∃ e, Stmt.eval fuel tbl ctx rt (.forLoop init cond post body) = .done (.error e) := by
  intro fuel
  cases fuel with
  | zero =>
    refine ⟨SolidityFailure.outOfFuel, ?_⟩
    first | rfl | (simp only [Stmt.eval]; done) | (simp only [Stmt.eval]; rfl)
  | succ f =>
    simp only [Stmt.eval]
    rcases hinit f with ⟨e, he⟩ | ⟨rt1, h1, hP⟩
    · rw [he]; exact ⟨e, rfl⟩
    · rw [h1, bind_done_ok]
      dsimp only
      obtain ⟨e, he⟩ := evalFor_err P h f rt1 hP
      rw [he]
      exact ⟨e, rfl⟩

theorem evalList_cons_err {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt : Runtime}
    {s : Stmt} {rest : List Stmt} {e : SolidityFailure}
    (h : Stmt.eval n tbl ctx rt s = .done (.error e)) :
    Stmt.evalList n tbl ctx rt (s :: rest) = .done (.error e) := by
  simp only [Stmt.evalList]
  rw [h]
  rfl

theorem eval_block_err {n : Nat} {tbl : FunctionTable} {ctx : Context} {rt : Runtime}
    {ss : List Stmt} {e : SolidityFailure} (h : Stmt.evalList n tbl ctx rt.pushScope ss = .done (.error e)) :
    Stmt.eval (n + 1) tbl ctx rt (.block ss) = .done (.error e) := by
  rw [Stmt.eval]
  simp only [h, bind, EvmCompiler.Simulation.Interaction.bind]

open SolidCore.Solidity SolidCore.Refinement SolidCore.Refinement.Generic

/-- **A call whose body fails at the fuel has no result**: the dispatcher folds the body's
interaction tree fail-closed, so an error (out of fuel among them) leaves `runtimeRun` empty. -/
theorem runtime_run_err {fuel : Nat} {c : TypeCheck.CheckedContract} {σ : List (Nat × Nat)}
    {sel : Nat} (hsel : sel < 2 ^ 32) {fn : FunctionDef}
    (hfind : c.core.findFunctionBySelector? sel = some fn) {ws : List Nat}
    (hw : widthsOf fn.params fn.paramAbiCleanups = some ws)
    (hret : fn.returns.all wordBinding = true)
    (args : List Nat)
    (hlen : args.length = fn.params.length) (hargs : ∀ a ∈ args, a < 2 ^ 256)
    (hclean : argsClean ws args = true)
    (hdec : ABI.decodeFunctionArgs? fn (Dirty.argBytes args) = .ok (args.map .word))
    (hb : ∀ ctx rt, StmtRel ⟨args, slotValue σ, solHash, callerWord⟩ { envOf c.core with facts := argFacts ws 0 } ctx rt
      (initState fn) → ∃ e, Stmt.eval fuel c.core.table ctx rt fn.body = .done (.error e)) :
    runtimeRun fuel c { calldata := Abi.calldata sel args, callvalue := 0, storage := σ } = none := by
  unfold runtimeRun runtimeResult?
  simp only [Dirty.bytes_calldata]
  have hwT := widthsOf_T hw
  obtain ⟨rt, hrel, hcall⟩ := call_entry (c := c) hwT.1 (retBinding_of_word hret) (tagsOk_of_words (words_of_widths hw hret)) fuel
    { c.core.context with sender := callerAddress, self := selfAddress, value := 0 } callerAddress
    ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args)
    (st0 := { State.empty with
      storage := σ.foldl (fun acc kv => StorageMap.insertLoop acc kv.1 kv.2) State.empty.storage })
    (getD_storage_empty σ) rfl
    (.lit callerWord) hlen hargs hclean (argFacts_hold ⟨args, slotValue σ, solHash, callerWord⟩ hargs ws 0 (by simpa using hclean)) rfl
  rw [argVals_words' (fun ty hty => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hty
      exact hwT.2 p hp) (by simpa using hlen)] at hcall
  obtain ⟨e, he⟩ := hb _ rt hrel
  have hdrop : ((EthLib.Base.natToBytes 4 sel).map (·.toNat) ++ Dirty.argBytes args).drop
      ABI.selectorBytes = Dirty.argBytes args := by
    simp [ABI.selectorBytes, EthLib.Base.natToBytes_length]
  simp only [ABI.Contract.callCalldataAtFromWithContext?, Dirty.readSelector_calldata _ hsel, hfind,
    hdrop, hdec, FunctionDef.call?, hcall, he]
  have hacc : fn.acceptsValue 0 = true := by simp [FunctionDef.acceptsValue, wordEq]
  rw [hacc, if_pos rfl]
  first | rfl | simp

/-- info: 'SolidCore.Refinement.Generic.Loop.runtime_run_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runtime_run_err

/-- info: 'SolidCore.Refinement.Generic.Loop.forLoop_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forLoop_err

end SolidCore.Refinement.Generic.Loop
