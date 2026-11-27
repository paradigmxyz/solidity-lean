import Verify.LoopSource.Proof.EraseLoop

/-!
# Counted loops in internal callees

`eraseLoopStmt` erases counted `for` loops in a body, but an internal call in that body is erased
by `eraseInc`, hence by `eraseStmt`, whose callee body has no loop case. `eraseLoopCall` is
`eraseLoopStmt` with one more case: a statement-position internal call (`eraseStmt`'s
`internalCall` case: word parameters and results, its arguments erased in order, then its callee's
body at the callee's frame, then its results assigned) whose callee's body is erased by
`eraseLoopCall` itself, and the `captureReturn` wrapper the frontend puts around such a call (its
body by `eraseLoopCall`, then `eraseStmt`'s `captureLeaf`), so a loop in an internal function the
body calls is erased in closed form as one in the body is.

* `runs_eraseLoopCall`: a statement runs as its `eraseLoopCall` erasure (`StmtRuns`), by the
  proofs of `runs_eraseLoop` (blocks, counted loops, every other statement by `eraseInc`) and of
  `eval_stmt`'s internal-call and `captureReturn` cases, by induction on the fuel.
* `bodyRuns_of_eraseLoopCall`: `BodyRuns` from `eraseLoopCall`, as `bodyRuns_of_eraseLoop`.

Each internal call takes one fuel and each counted loop `loopFuel` more than its body, so a body
whose loop sits in a callee erases at a fuel above `2 ^ 256` plus its nesting. Outside these cases
the erasure is `eraseInc`'s, and `none` outside the shape.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-- **The erasure of a statement with counted loops, in its body or in the internal functions it
calls**, with fuel `n`: `eraseLoopStmt` with statement-position internal calls whose callee's body
is erased by `eraseLoopCall`. -/
def eraseLoopCall (E : EraseEnv) : Nat → Stmt → SymState → Option Br
  | 0, _, _ => none
  | n + 1, s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (eraseLoopCall E n) ss S.push
      some (b.mapS SymState.pop)
    | .forLoop init cnd post body =>
      if loopFuel ≤ n then do
        let bi ← eraseInc E n init S.push
        let b ← bi.bind (accelFor E (n - loopFuel) cnd post body)
        some (b.mapS SymState.pop)
      else none
    | .internalCall targets callee args => do
      let fn ← E.tbl.lookup? callee
      if fn.params.all wordDecl && fn.returns.all wordDecl && args.length = fn.params.length then
        let (gs, vs) ← eraseExprs E.fields S args
        let b ← eraseLoopCall E n fn.body
          { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs, caller := S.caller }
        let b' ← b.bindLeaf (callLeaf fn targets S)
        some (guards gs b')
      else none
    | .captureReturn names body => do
      let b ← eraseLoopCall E n body S
      b.bindLeaf (captureLeaf names)
    | s => eraseInc E (n + 1) s S

/-- Split on whether the overflow conditions `c` fire (`SourceStmt.lean`'s local macro). -/
local macro "guard_cases " h:ident " : " c:term : tactic => `(tactic|
  (by_cases $h:ident : $c = true
   focus
     simp only [$h:ident, ↓reduceIte, Bool.true_or, Bool.or_true, Bool.or_assoc]
     first
       | exact ⟨_, rfl, rfl⟩
       | exact ⟨.reverted _ (.panic 0x11), by split <;> (try split) <;> first | rfl | simp_all, rfl⟩
   simp only [$h:ident, Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false,
     Bool.or_assoc]))

/-- **A statement runs as its `eraseLoopCall` erasure.** -/
theorem runs_eraseLoopCall (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseLoopCall E n s S = some b → StmtRuns E n ctx s S b
  | 0, _, _, _, h => by simp [eraseLoopCall] at h
  | n + 1, s, S, b, h => by
    unfold eraseLoopCall at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block (runs_eraseLoopCall E ctx n) h1
    · rename_i init cnd post body
      split at h
      · rename_i hfuel
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨bi, hbi, b', hb', rfl⟩ := h
        intro σ rt hrel
        obtain ⟨r0, hr0, hl0⟩ := runs_eraseInc E ctx n init S.push bi hbi σ rt.pushScope hrel.pushScope
        have hbe := Br.bind_eval σ hb'
        rw [Br.eval_mapS]
        revert hl0 hbe
        cases bi.eval σ with
        | normal S1 =>
          intro hl0 hbe
          obtain ⟨c, hc, hce⟩ := hbe
          cases r0 <;> simp only [LeafRel] at hl0
          rename_i rt1
          obtain ⟨base, slots, gs, S2, trs, ji, bnd, js, hS, hK, hit, hS2, hcv, hji, htr, hbnd, hjs,
            hall, rfl⟩ := accelFor_spec hc
          have hlf : loopFuel = wordSize + 1 := rfl
          obtain ⟨r, hr, hl⟩ := runs_accel hS hK hit hS2 hcv hji htr hbnd hjs hall hr0 hl0 (n + 1)
            (by omega) (by omega)
          exact ⟨_, hr, by rw [hce]; exact hl.popScope⟩
        | returned S1 vs =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by rw [hbe]; exact LeafRel.popScope hl0⟩
        | reverted p =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by
            rw [hbe]; exact LeafRel.popScope (l := .reverted p) (by simpa only [LeafRel] using hl0)⟩
      · cases h
    · rename_i targets callee args
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨fn, hfn, h⟩ := h
      split at h
      case isFalse => simp at h
      rename_i hshape
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨gs, vs⟩, hargs, b0, hb0, b1, hb1, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hshape
      have hp : fn.params.all wordDecl = true := hshape.1.1
      have hr : fn.returns.all wordDecl = true := hshape.1.2
      have hvl : vs.length = fn.params.length := (eraseExprs_length hargs).trans hshape.2
      intro ρ rt hrel
      have hev := eval_refArgs ρ E.fields ctx rt S hrel.expr hargs
      rw [Stmt.eval]
      simp only [hev]
      rw [guards_eval]
      guard_cases hg : gs.any (fun g => g.eval ρ != 0)
      simp only [caught_done_ok, bind_done_ok, hfn, internalCallEnter?,
        initialFrame_words ρ fn vs hp hr hvl]
      have hctx : ({ ctx with checked := true } : Context) = ctx := by
        rw [show true = ctx.checked from hrel.checked.symm]
      have hrel0 : StmtRel ρ E ctx { rt with locals := [frameOf ρ (callFrame fn vs)] }
          { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs, caller := S.caller } :=
        { hrel with frames := rfl }
      obtain ⟨r0, hr0, hl0⟩ := runs_eraseLoopCall E ctx n fn.body _ b0 hb0 ρ _ hrel0
      rw [hctx, hr0, bind_done_ok]
      obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ hb1
      rw [hce]
      exact finish_call hrel hr r0 _ c hl0 hc
    · rename_i names body
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨b0, hb0, h⟩ := h
      intro ρ rt hrel
      obtain ⟨r0, hr0, hl0⟩ := runs_eraseLoopCall E ctx n body S b0 hb0 ρ rt hrel
      obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ h
      obtain ⟨r, hr, hl⟩ := capture_ok names r0 (b0.eval ρ) c hl0 hc
      refine ⟨r, ?_, hce ▸ hl⟩
      rw [Stmt.eval]
      simp only [hr0, bind_done_ok]
      exact hr
    · exact runs_eraseInc E ctx (n + 1) s S b h

/-- **A body with counted loops, in itself or in its internal callees, runs as its erasure**:
`BodyRuns` from `eraseLoopCall`. -/
theorem bodyRuns_of_eraseLoopCall {E : EraseEnv} {fuel : Nat} {fn : FunctionDef} {b : Br}
    (h : eraseLoopCall E fuel fn.body (initState fn) = some b) : BodyRuns E fuel fn b :=
  fun ρ ctx rt hrel => runs_eraseLoopCall E ctx fuel fn.body (initState fn) b h ρ rt hrel

end SolidCore.Refinement.Generic.Loop

/-- info: 'SolidCore.Refinement.Generic.Loop.runs_eraseLoopCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.runs_eraseLoopCall

/-- info: 'SolidCore.Refinement.Generic.Loop.bodyRuns_of_eraseLoopCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SolidCore.Refinement.Generic.Loop.bodyRuns_of_eraseLoopCall
