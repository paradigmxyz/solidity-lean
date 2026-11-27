import Verify.Generic.CtorWords
import Verify.LoopSource.Proof.EraseLoopCall

/-!
# A constructor with counted loops, for every argument list

`Verify/Generic/CtorWords.lean` states the deployment of a constructor with static word parameters
for every argument list from one erasure of its body by `eraseStmt`, which has no loop case. This
module states the same deployment from the erasure by `Loop.eraseLoopCall`
(`Verify/LoopSource/Proof/EraseLoopCall.lean`): `eraseLoopStmt`, which erases counted `for` loops
in closed form, extended to internal calls whose callee's body it erases too (`runs_eraseLoopCall`:
a statement runs as that erasure, at the same fuel). A loop only creation runs (in the constructor,
its modifiers or the internal functions it calls) leaves no loop in the runtime bytecode: only the
deployment changes, so the rest of the generic route (`Shapes.compiledArgs`) applies unchanged.

* `construct_of_eraseLoop`: SolidCore's constructor on every list of argument words runs as the
  `eraseLoopCall` erasure of its body; the proof is `construct_of_erase`'s with
  `runs_eraseLoopCall` in place of `eval_stmt`.
* `loadDeployed_of_normalsL`, `returns_of_evalL`: the deployment where the constructor returns,
  and that it returns where the tree's leaf is normal, as in `CtorWords.lean`.
* `ctorLeafL`, `ctorShapeOfL` and `deployed_of_ctorShapeOfL`: what a generated module evaluates
  once in the kernel, and the deployment for every argument list it gives. The conclusion of
  `deployed_of_ctorShapeOfL` is word for word `deployed_of_ctorShapeOf`'s.

The erasure needs fuel: a counted loop takes `Loop.loopFuel = 2 ^ 256 + 1` more than its body, so a
module states these at a fuel above `2 ^ 256` (the driver uses `2 ^ 256 + 64`), and `CtorReturns
fuel` is then the constructor's return at that fuel. Nothing outside the erasure's shape is
admitted: `eraseLoopCall` is `none` there and `ctorShapeOfL` is `false`.
-/

namespace SolidCore.Refinement.Generic

open EthLib.Base EthLib.Execution EthLib.Execution.Evm
open SolarTV SolarTV.Machine SolarTV.MIR.Lowered SolidCore.Solidity SolidCore.Solidity.Source
open SolidCore.Refinement SolidCore.Refinement.Abi SolidCore.Refinement.Evm

/-- **SolidCore's constructor on an argument list runs as its body's `eraseLoopCall` erasure**:
`construct_of_erase` for bodies with counted loops. -/
theorem construct_of_eraseLoop {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br}
    (herase : Loop.eraseLoopCall { envOf c.core with facts := argFacts wds 0 } fuel fn.body
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
      frames := rfl
      store := by
        intro k _
        simp [State.loadSlot, StorageMap.lookup?, State.empty, Writes.store, initState, hρ]
      logs := by simp [State.empty, initState]
      facts := argFacts_hold ρ hargs' wds 0 (by simpa [hρ] using hclean) }
  obtain ⟨r, hrun, hleaf⟩ := Loop.runs_eraseLoopCall E ctx fuel fn.body _ _ herase ρ _ hrel
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

/-- **The deployment on an argument list on which the constructor returns**, from an
`eraseLoopCall` erasure all of whose leaves are normal with the writes `W` and no logs, or reverts:
`loadDeployed_of_normals` for bodies with counted loops. -/
theorem loadDeployed_of_normalsL {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br} {W : Writes}
    (herase : Loop.eraseLoopCall { envOf c.core with facts := argFacts wds 0 } fuel fn.body
      { initState fn with caller := .lit selfAddress } = some b)
    (hn : normalsOnly W b = true)
    {ws : List Nat} (hlen : ws.length = fn.params.length) (hargs : ∀ a ∈ ws, a < 2 ^ 256)
    (hclean : argsClean wds ws = true)
    (hret : ∃ d vs, Source.deployArgs? fuel ws c = some (CallResult.returned d vs)) :
    ∃ d, Loop.LoadDeployed fuel c ws d ∧
      ∀ k, d.loadSlot k = Writes.store ⟨ws, fun _ => 0, solHash, callerWord⟩ W k := by
  obtain ⟨ctx, r, hcons, hleaf⟩ := construct_of_eraseLoop hf hps hret0 herase hlen hargs hclean
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

/-- **The constructor returns where the `eraseLoopCall` erasure's leaf is normal.** -/
theorem returns_of_evalL {fuel : Nat} {c : TypeCheck.CheckedContract} {fn : FunctionDef}
    (hf : TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl = some fn)
    (hps : ∀ p ∈ fn.params, (p.ty = .uint256 ∨ p.ty = .address) ∧ p.isStorageRef = false)
    (hret0 : fn.returns = []) {wds : List Nat} {b : Br}
    (herase : Loop.eraseLoopCall { envOf c.core with facts := argFacts wds 0 } fuel fn.body
      { initState fn with caller := .lit selfAddress } = some b)
    {ws : List Nat} (hlen : ws.length = fn.params.length) (hargs : ∀ a ∈ ws, a < 2 ^ 256)
    (hclean : argsClean wds ws = true) {S : SymState}
    (hS : b.eval ⟨ws, fun _ => 0, solHash, callerWord⟩ = .normal S) :
    ∃ d vs, Source.deployArgs? fuel ws c = some (CallResult.returned d vs) := by
  obtain ⟨ctx, r, hcons, hleaf⟩ := construct_of_eraseLoop hf hps hret0 herase hlen hargs hclean
  rw [hS] at hleaf
  cases r <;> simp only [LeafRel] at hleaf
  rename_i rt
  exact ⟨rt.state, [], by rw [hcons, callBodyResult_normal hret0]⟩

/-- Whether the constructor `fn`, with widths `wds`, erases by `eraseLoopCall` to the tree `b`,
every leaf of which is normal with the writes `W` and no logs, or a revert: `ctorLeaf` for bodies
with counted loops. -/
def ctorLeafL (core : Contract) (fuel : Nat) (fn : FunctionDef) (wds : List Nat) (b : Br)
    (W : Writes) : Bool :=
  wordParams fn.params && fn.returns.isEmpty && widthsOf fn.params fn.paramAbiCleanups == some wds &&
    Loop.eraseLoopCall { envOf core with facts := argFacts wds 0 } fuel fn.body
        { initState fn with caller := .lit selfAddress } == some b && normalsOnly W b

/-- The core of the checked contract `c?`, and whether its constructor erases by `eraseLoopCall`,
with the widths `wds`, to the tree `b` whose leaves are normal with the writes `W` and no logs, or
revert; `none` when it does not check. `ctorShapeOf` for bodies with counted loops. -/
def ctorShapeOfL (fuel : Nat) (c? : Except TypeCheck.TypeError TypeCheck.CheckedContract)
    (wds : List Nat) (b : Br) (W : Writes) : Option (Contract × Bool) :=
  match c? with
  | .ok c => some (c.core,
      match TypeCheck.CheckedProgram.constructorFunctionFor? c.program c.decl with
      | some fn => ctorLeafL c.core fuel fn wds b W
      | none => false)
  | .error _ => none

/-- **The deployment for every argument list**, from one kernel evaluation of `ctorShapeOfL`:
`deployed_of_ctorShapeOf`'s conclusion, for a constructor body with counted loops. -/
theorem deployed_of_ctorShapeOfL {fuel : Nat}
    {c? : Except TypeCheck.TypeError TypeCheck.CheckedContract} {wds : List Nat} {b : Br}
    {W : Writes} {core : Contract} {c : TypeCheck.CheckedContract}
    (h : ctorShapeOfL fuel c? wds b W = some (core, true)) (hc : c? = .ok c) :
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
  unfold ctorLeafL at hb
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hb
  obtain ⟨⟨⟨⟨hwp, hr⟩, hw⟩, herase⟩, hn⟩ := hb
  have hps := wordParams_spec hwp
  refine ⟨hk, fun ws hlen hargs hclean hret => ?_, fun ws hlen hargs hclean hnorm => ?_⟩
  · obtain ⟨c', hc', hret'⟩ := hret
    cases hc'
    obtain ⟨d, hd, hloads⟩ := loadDeployed_of_normalsL hf hps hr herase hn
      (hlen.trans (widthsOf_length hw)) hargs hclean hret'
    exact ⟨d, hd, fun σ hcov => coversLoad_of_writes hloads hcov⟩
  · obtain ⟨S, hS⟩ := normalAt_spec hnorm
    exact ⟨_, rfl, returns_of_evalL hf hps hr herase (hlen.trans (widthsOf_length hw)) hargs hclean hS⟩

end SolidCore.Refinement.Generic

/-- info: 'SolidCore.Refinement.Generic.construct_of_eraseLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.construct_of_eraseLoop

/-- info: 'SolidCore.Refinement.Generic.deployed_of_ctorShapeOfL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.deployed_of_ctorShapeOfL
