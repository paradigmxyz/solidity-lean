import Verify.LoopSource.Proof.EraseLoop

/-!
# Counted loops in internal callees, and loops of a constant trip count

`eraseLoopStmt` erases counted `for` loops in a body, but an internal call in that body is erased
by `eraseInc`, hence by `eraseStmt`, whose callee body has no loop case, and a loop whose iteration
is outside the counted shape (it adds the counter to a word, say) is not erased at all.
`eraseLoopCall` is `eraseLoopStmt` with three more cases:

* a statement-position internal call (`eraseStmt`'s `internalCall` case: word parameters and
  results, its arguments erased in order, then its callee's body at the callee's frame, then its
  results assigned) whose callee's body is erased by `eraseLoopCall` itself;
* the `captureReturn` wrapper the frontend puts around such a call (its body by `eraseLoopCall`,
  then `eraseStmt`'s `captureLeaf`);
* a `for` loop outside `accelFor`'s counted shape whose condition is a **closed** word at every
  iteration (no argument, storage, caller or hash word: `closedW`, so its value is the same at
  every valuation, `eval_closedW`) and has no overflow guard: the loop is **unrolled**, one
  iteration (body, then update, each erased by `eraseLoopCall`) per iteration of SolidCore's
  `Stmt.evalFor`, at the fuel `evalFor` runs them with, until the condition is zero, for at most
  `unrollBudget` iterations. The iterations' guards, reverts and returns stay in the tree.

* `runs_eraseLoopCall`: a statement runs as its `eraseLoopCall` erasure (`StmtRuns`), by induction
  on the fuel over statements and unrolled loops together (`eraseJob`, `JobRuns`): blocks, counted
  loops and every other statement as `runs_eraseLoop` proves them, internal calls and
  `captureReturn` as `eval_stmt` does, and an unrolled loop by `Stmt.evalFor`'s own steps.
* `bodyRuns_of_eraseLoopCall`: `BodyRuns` from `eraseLoopCall`, as `bodyRuns_of_eraseLoop`.

Each internal call takes one fuel, each counted loop `loopFuel` more than its body and each unrolled
iteration one, so a body whose loop sits in a callee erases at a fuel above `2 ^ 256` plus its
nesting. Outside these cases the erasure is `eraseInc`'s, and `none` outside the shape.
-/

namespace SolidCore.Refinement.Generic.Loop
open SolidCore.Solidity.Source SolidCore.Refinement.Generic

/-- Whether a word mentions no argument, storage, caller or hash word: its value is the same at
every valuation (`eval_closedW`). -/
def closedW : WExpr → Bool
  | .lit _ => true
  | .arg _ => false
  | .init _ => false
  | .un _ a => closedW a
  | .bin _ a b => closedW a && closedW b
  | .sinit _ => false
  | .sel c a b => closedW c && closedW a && closedW b
  | .hash _ _ => false
  | .caller => false

/-- **A closed word has one value.** -/
theorem eval_closedW {e : WExpr} (h : closedW e = true) (ρ ρ' : Val) : e.eval ρ = e.eval ρ' := by
  induction e with
  | lit _ => rfl
  | arg _ => simp [closedW] at h
  | init _ => simp [closedW] at h
  | un op a ih => simp only [closedW] at h; simp only [WExpr.eval, ih h]
  | bin op a b iha ihb =>
    simp only [closedW, Bool.and_eq_true] at h
    simp only [WExpr.eval, iha h.1, ihb h.2]
  | sinit _ => simp [closedW] at h
  | sel c a b ihc iha ihb =>
    simp only [closedW, Bool.and_eq_true] at h
    simp only [WExpr.eval, ihc h.1.1, iha h.1.2, ihb h.2]
  | hash _ _ => simp [closedW] at h
  | caller => simp [closedW] at h

/-- The valuation the erasure evaluates a closed condition at (any other gives the same value). -/
def valZero : Val := ⟨[], fun _ => 0, solHash, 0⟩

/-- At most this many iterations of a loop are unrolled. -/
def unrollBudget : Nat := 256

/-- What the erasure erases: a statement, or the rest of a `for` loop to unroll (its condition,
update and body, and how many more iterations it may unroll), from the state at its condition. -/
inductive EraseJob where
  | stmt (s : Stmt)
  | loop (cnd : Expr) (post body : Stmt) (u : Nat)

/-- `eraseLoopStmt`'s erasure of a counted `for` loop at fuel `n + 1` (`accelFor`). -/
def accelLoop (E : EraseEnv) (n : Nat) (init : Stmt) (cnd : Expr) (post body : Stmt)
    (S : SymState) : Option Br :=
  if loopFuel ≤ n then do
    let bi ← eraseInc E n init S.push
    let b ← bi.bind (accelFor E (n - loopFuel) cnd post body)
    some (b.mapS SymState.pop)
  else none

/-- **The erasure of a job** with fuel `n`: statements as `eraseLoopStmt` does, internal calls and
their `captureReturn` wrapper with the callee's body erased here too, and a `for` loop outside the
counted shape unrolled while its condition is closed (the `loop` job: one iteration, then the rest
at one fuel less, as `Stmt.evalFor` runs it). -/
def eraseJob (E : EraseEnv) : Nat → EraseJob → SymState → Option Br
  | 0, _, _ => none
  | n + 1, .stmt s, S =>
    match s with
    | .block ss => do
      let b ← eraseSeq (fun s S => eraseJob E n (.stmt s) S) ss S.push
      some (b.mapS SymState.pop)
    | .forLoop init cnd post body =>
      match accelLoop E n init cnd post body S with
      | some b => some b
      | none => do
        let bi ← eraseJob E n (.stmt init) S.push
        let b ← bi.bind (eraseJob E n (.loop cnd post body unrollBudget))
        some (b.mapS SymState.pop)
    | .internalCall targets callee args => do
      let fn ← E.tbl.lookup? callee
      if fn.params.all wordDecl && fn.returns.all wordDecl && args.length = fn.params.length then
        let (gs, vs) ← eraseExprs E.fields S args
        let b ← eraseJob E n (.stmt fn.body)
          { scopes := [callFrame fn vs], writes := S.writes, logs := S.logs, caller := S.caller }
        let b' ← b.bindLeaf (callLeaf fn targets S)
        some (guards gs b')
      else none
    | .captureReturn names body => do
      let b ← eraseJob E n (.stmt body) S
      b.bindLeaf (captureLeaf names)
    | s => eraseInc E (n + 1) s S
  | n + 1, .loop cnd post body u, S =>
    match u with
    | 0 => none
    | u + 1 => do
      let (gs, v) ← eraseExpr E.fields S cnd
      if gs.isEmpty && closedW v then
        if v.eval valZero = 0 then some (.leaf (.normal S))
        else do
          let bb ← eraseJob E n (.stmt body) S
          bb.bind fun S1 => do
            let bp ← eraseJob E n (.stmt post) S1
            bp.bind (eraseJob E n (.loop cnd post body u))
      else none

/-- **The erasure of a statement with counted loops, unrolled loops of a closed condition, and
both in the internal functions it calls**, with fuel `n`. -/
def eraseLoopCall (E : EraseEnv) (n : Nat) (s : Stmt) (S : SymState) : Option Br :=
  eraseJob E n (.stmt s) S

/-- What a job's erasure promises: a statement runs as it (`StmtRuns`); the rest of a loop, run by
`Stmt.evalFor` with the job's fuel, ends as it. -/
def JobRuns (E : EraseEnv) (n : Nat) (ctx : Context) : EraseJob → SymState → Br → Prop
  | .stmt s, S, b => StmtRuns E n ctx s S b
  | .loop cnd post body _, S, b => ∀ σ rt, StmtRel σ E ctx rt S →
      ∃ r, Stmt.evalFor n E.tbl ctx rt cnd post body = .done (.ok r) ∧ LeafRel σ E ctx r (b.eval σ)

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

/-- `eraseLoopStmt`'s counted loop runs as its erasure. -/
theorem runs_accelLoop {E : EraseEnv} {ctx : Context} {n : Nat} {init : Stmt} {cnd : Expr}
    {post body : Stmt} {S : SymState} {b : Br} (h : accelLoop E n init cnd post body S = some b) :
    StmtRuns E (n + 1) ctx (.forLoop init cnd post body) S b := by
  unfold accelLoop at h
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

/-- **A job runs as its erasure.** -/
theorem runs_eraseJob (E : EraseEnv) (ctx : Context) :
    ∀ n j S b, eraseJob E n j S = some b → JobRuns E n ctx j S b
  | 0, _, _, _, h => by simp [eraseJob] at h
  | n + 1, .stmt s, S, b, h => by
    have ih : ∀ s S b, eraseJob E n (.stmt s) S = some b → StmtRuns E n ctx s S b :=
      fun s S b h => runs_eraseJob E ctx n (.stmt s) S b h
    show StmtRuns E (n + 1) ctx s S b
    unfold eraseJob at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b1, h1, rfl⟩ := h
      exact runs_block ih h1
    · rename_i init cnd post body
      split at h
      · rename_i b' ha
        simp only [Option.some.injEq] at h
        subst h
        exact runs_accelLoop ha
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨bi, hbi, b', hb', rfl⟩ := h
        intro σ rt hrel
        obtain ⟨r0, hr0, hl0⟩ := ih init S.push bi hbi σ rt.pushScope hrel.pushScope
        have hbe := Br.bind_eval σ hb'
        rw [Br.eval_mapS]
        revert hl0 hbe
        cases bi.eval σ with
        | normal S1 =>
          intro hl0 hbe
          obtain ⟨c, hc, hce⟩ := hbe
          cases r0 <;> simp only [LeafRel] at hl0
          rename_i rt1
          obtain ⟨r, hr, hl⟩ := runs_eraseJob E ctx n (.loop cnd post body unrollBudget) S1 c hc σ rt1 hl0
          refine ⟨r.mapRuntime Runtime.popScope, ?_, by rw [hce]; exact hl.popScope⟩
          simp only [Stmt.eval]
          rw [hr0, bind_done_ok]
          simp only [hr, bind_done_ok]
          rfl
        | returned S1 vs =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by rw [hbe]; exact LeafRel.popScope hl0⟩
        | reverted p =>
          intro hl0 hbe
          cases r0 <;> simp only [LeafRel] at hl0
          exact ⟨_, forLoop_stop hr0 (fun _ h => by cases h), by
            rw [hbe]; exact LeafRel.popScope (l := .reverted p) (by simpa only [LeafRel] using hl0)⟩
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
      obtain ⟨r0, hr0, hl0⟩ := ih fn.body _ b0 hb0 ρ _ hrel0
      rw [hctx, hr0, bind_done_ok]
      obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ hb1
      rw [hce]
      exact finish_call hrel hr r0 _ c hl0 hc
    · rename_i names body
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨b0, hb0, h⟩ := h
      intro ρ rt hrel
      obtain ⟨r0, hr0, hl0⟩ := ih body S b0 hb0 ρ rt hrel
      obtain ⟨c, hc, hce⟩ := Br.bindLeaf_eval ρ h
      obtain ⟨r, hr, hl⟩ := capture_ok names r0 (b0.eval ρ) c hl0 hc
      refine ⟨r, ?_, hce ▸ hl⟩
      rw [Stmt.eval]
      simp only [hr0, bind_done_ok]
      exact hr
    · exact runs_eraseInc E ctx (n + 1) s S b h
  | n + 1, .loop cnd post body 0, S, b, h => by simp [eraseJob] at h
  | n + 1, .loop cnd post body (u + 1), S, b, h => by
    show ∀ σ rt, StmtRel σ E ctx rt S →
      ∃ r, Stmt.evalFor (n + 1) E.tbl ctx rt cnd post body = .done (.ok r) ∧ LeafRel σ E ctx r (b.eval σ)
    simp only [eraseJob, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨gs, v⟩, hc, h⟩ := h
    split at h
    case isFalse => simp at h
    rename_i hcl
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hcl
    obtain ⟨rfl, hcw⟩ := hcl
    intro σ rt hrel
    have heval := eval_eq σ E.fields ctx rt S hrel.expr hc
    have hv : v.eval σ = v.eval valZero := eval_closedW hcw σ valZero
    have hn : SolidCore.Solidity.Shared.norm (v.eval σ) = v.eval σ := norm_lt (v.eval_lt σ)
    have hcond : (Expr.eval ctx rt cnd).caught = .done (.ok (.ok (.word (v.eval σ), rt))) := by
      rw [heval, caught_exprResult]
      simp
    split at h
    · rename_i h0
      simp only [Option.some.injEq] at h
      subst h
      have hz : v.eval σ = 0 := by rw [hv]; simpa using h0
      refine ⟨.normal rt, ?_, hrel⟩
      simp only [Stmt.evalFor]
      simp only [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hz]
      rfl
    · rename_i h0
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨bb, hbb, hb⟩ := h
      have hnz : ¬ v.eval σ = 0 := by
        rw [hv]; simpa using h0
      obtain ⟨r1, hr1, hl1⟩ := runs_eraseJob E ctx n (.stmt body) S bb hbb σ rt hrel
      have hbe := Br.bind_eval σ hb
      revert hl1 hbe
      cases bb.eval σ with
      | normal S1 =>
        intro hl1 hbe
        obtain ⟨c, hc1, hce⟩ := hbe
        cases r1 <;> simp only [LeafRel] at hl1
        rename_i rt1
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hc1
        obtain ⟨bp, hbp, hc2⟩ := hc1
        obtain ⟨r2, hr2, hl2⟩ := runs_eraseJob E ctx n (.stmt post) S1 bp hbp σ rt1 hl1
        have hbe2 := Br.bind_eval σ hc2
        revert hl2 hbe2
        cases bp.eval σ with
        | normal S2 =>
          intro hl2 hbe2
          obtain ⟨c', hc3, hce'⟩ := hbe2
          cases r2 <;> simp only [LeafRel] at hl2
          rename_i rt2
          obtain ⟨r3, hr3, hl3⟩ := runs_eraseJob E ctx n (.loop cnd post body u) S2 c' hc3 σ rt2 hl2
          refine ⟨r3, ?_, by rw [hce, hce']; exact hl3⟩
          simp only [Stmt.evalFor]
          simp [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hnz, hr1, hr2, hr3] <;> rfl
        | returned S2 vs =>
          intro hl2 hbe2
          cases r2 <;> simp only [LeafRel] at hl2
          rename_i rt2 vs2
          refine ⟨.returned rt2 vs2, ?_, by rw [hce, hbe2]; exact hl2⟩
          simp only [Stmt.evalFor]
          simp [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hnz, hr1, hr2] <;> rfl
        | reverted p =>
          intro hl2 hbe2
          cases r2 <;> simp only [LeafRel] at hl2
          rename_i rt2 d
          refine ⟨.reverted rt2 d, ?_, by rw [hce, hbe2]; exact hl2⟩
          simp only [Stmt.evalFor]
          simp [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hnz, hr1, hr2] <;> rfl
      | returned S1 vs =>
        intro hl1 hbe
        cases r1 <;> simp only [LeafRel] at hl1
        rename_i rt1 vs1
        refine ⟨.returned rt1 vs1, ?_, by rw [hbe]; exact hl1⟩
        simp only [Stmt.evalFor]
        simp [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hnz, hr1] <;> rfl
      | reverted p =>
        intro hl1 hbe
        cases r1 <;> simp only [LeafRel] at hl1
        rename_i rt1 d
        refine ⟨.reverted rt1 d, ?_, by rw [hbe]; exact hl1⟩
        simp only [Stmt.evalFor]
        simp [hcond, bind_done_ok, Value.expectWord, hn, wordTruthy, hnz, hr1] <;> rfl

/-- **A statement runs as its `eraseLoopCall` erasure.** -/
theorem runs_eraseLoopCall (E : EraseEnv) (ctx : Context) :
    ∀ n s S b, eraseLoopCall E n s S = some b → StmtRuns E n ctx s S b :=
  fun n s S b h => runs_eraseJob E ctx n (.stmt s) S b h

/-- **A body with counted loops, unrolled loops, and both in its internal callees, runs as its
erasure**: `BodyRuns` from `eraseLoopCall`. -/
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
