import SolidCore.Refinement.Wide.Source

/-!
# Lane B: `Sym.simp` in place of the repeated `Meta.simp` of `Wide.Tactic.evalGoal`

`src_symex_sym [lemmas]` / `wide_symex_sym [lemmas]` keep the outer structure of
`src_symex` / `wide_symex` (`SolidCore/Refinement/Wide/Tactic.lean`): evaluate a goal to a fixed
point, then split on the innermost closed `if` condition (`by_cases`) or else the first `match`
(`split`), close branches whose path conditions contradict by `omega`, and recurse to depth 16.
Only the evaluation step changes:

* **One `SymM` session for the whole tactic.** The `Sym` context and state (hash-consing table,
  `inferType`/congruence caches) are captured once and threaded through every goal, so pointers
  stay maximally shared across rounds, splits and sibling goals.
* **One `Sym.Simp.State` (persistent cache) for the whole tactic.** `Sym.Simp.SimpM.run` (not
  the convenience `Sym.simp`, which starts fresh) takes and returns the state.
* **On-demand unfolding without a growing theorem set.** Instead of re-collecting
  `unfoldableIn` of the goal and adding equations to one simp set each round, the `post`
  simproc unfolds an application whose head passes the *same* gate (`unfoldable`, the monad
  helpers, the monad instances, and the definitions named in the lemma list) with that
  constant's own equation theorems (`Cbv.getEqnTheorems`, cached per constant in the
  environment), falling back to its unfold equation for definitions not by well-founded
  recursion. The rules a term can use are a function of its head constant, so a cached result
  never goes stale when a new definition appears in the goal.
* **Control flow** (`ite`/`dite`/`cond`, matchers) goes through `simpControl` / `Cbv.tryMatcher`
  in `pre`: only conditions and discriminants are simplified, branches are left for the split.
* **Hypotheses** are rewrite rules of their goal. The cache records the hypotheses it was built
  under; when the next goal's differ, every cache entry whose key or result contains the
  left-hand side of a hypothesis that was added or removed, or whose proof mentions a removed
  hypothesis, is dropped (a full reset when a hypothesis has pattern variables). Sibling goals
  of a split share every entry that does not involve the split condition, and never see a proof
  that mentions the other sibling's hypothesis.
* **Library simp lemmas** (the default `@[simp]` set that `baseTheorems` starts from) are reached
  through a bridge: the Meta discrimination tree proposes candidates for the current term, and
  each candidate is converted to a `Sym.Simp.Theorem` once (memoised; lemmas Sym cannot use are
  counted as conversion failures).
* **`decide := true`** is emulated for closed propositions by evaluating `Decidable.decide` with
  `whnf` at default transparency (`of_decide_eq_true rfl`).
* **Fallback:** after the Sym rounds, the existing `Meta.simp` loop (a copy of `Wide.evalGoal`)
  runs on the result. Its progressing rounds are counted, so a run with zero fallback rounds is
  full Sym coverage; `nofallback` disables it (`nobridge`: no library bridge; `noshare`: a fresh
  cache per goal).
-/

open Lean Meta Elab Tactic
open Lean.Meta.Sym (SymM ExprPtr isSameExpr)
open Lean.Meta.Sym.Simp

namespace Verify.Eval.B
open SolidCore.Refinement.Wide

/-! ## Counters -/

structure Counters where
  goals : Nat := 0
  symRounds : Nat := 0
  symProgressRounds : Nat := 0
  symErrors : Nat := 0
  symClosed : Nat := 0
  symSteps : Nat := 0
  eqnRw : Nat := 0
  unfoldRw : Nat := 0
  deltaRw : Nat := 0
  lemmaRw : Nat := 0
  hypRw : Nat := 0
  bridgeRw : Nat := 0
  bridgeConverted : Nat := 0
  bridgeConvFail : Nat := 0
  projRw : Nat := 0
  betaRw : Nat := 0
  zetaRw : Nat := 0
  decideRw : Nat := 0
  cacheKept : Nat := 0
  cacheDropped : Nat := 0
  cacheResets : Nat := 0
  cacheFinal : Nat := 0
  fallbackGoals : Nat := 0
  fallbackRounds : Nat := 0
  fallbackClosed : Nat := 0
  splits : Nat := 0
  omegaClosed : Nat := 0
  symMs : Nat := 0
  invalidateMs : Nat := 0
  fallbackMs : Nat := 0
  deriving Repr

/-! ## Session -/

structure Session where
  symCtx : Sym.Context
  symState : Sym.State
  simpState : Sym.Simp.State := {}
  /-- The hypotheses (fvar, shared left-hand side or `none` for a non-ground one) the persistent
  cache was built under. -/
  cacheHyps : Array (FVarId × Option Expr) := #[]

structure Env where
  counters : IO.Ref Counters
  session : IO.Ref Session
  gateMemo : IO.Ref (NameMap Bool)
  bridgeMemo : IO.Ref (NameMap Bool)
  bridgeSet : IO.Ref Theorems
  userUnfold : NameSet
  userThms : Theorems
  simpThms : SimpTheorems
  bridge : Bool
  fallback : Bool
  share : Bool
  maxSteps : Nat
  debug : Bool := false
  decide : Bool := true
  deadline : Nat := 0
  kindMs : IO.Ref (Std.HashMap String Nat)
  log : IO.Ref (Array MessageData)

def bump (env : Env) (f : Counters → Counters) : IO Unit := env.counters.modify f

/-- Runs a `SymM` action in the tactic's session. -/
def runSym (env : Env) (x : SymM α) : MetaM α := do
  let s ← env.session.get
  let (a, st) ← (x s.symCtx).run s.symState
  env.session.modify fun s => { s with symState := st }
  return a

/-! ## The unfolding gate (same predicate as `Wide.unfoldableIn`) -/

def gate (env : Env) (n : Name) : MetaM Bool := do
  if env.userUnfold.contains n then return true
  if let some b := (← env.gateMemo.get).find? n then return b
  let b ← (do return (← unfoldable n) || monadHelpers.contains n || (← isMonadInstance n))
  env.gateMemo.modify (·.insert n b)
  return b

def isWF (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  let some v := ci.value? | return false
  return v.getUsedConstants.contains ``WellFounded.fix

/-- Recursive (structural, well-founded or mutual): such a definition is unfolded only by its
equation theorems, whose left-hand sides need constructor arguments, as `Meta.simp` does. Its
unfold equation would unfold it on any argument, and on a partial application. -/
def isRecLike (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  let some v := ci.value? | return false
  if ci.all.length > 1 then return true
  return v.getUsedConstants.any fun c =>
    c == ``WellFounded.fix || c == n || c.isStr && (c.getString! == "brecOn" || c.getString! == "binductionOn")

/-! ## Simprocs -/

def countStep (env : Env) (f : Counters → Counters) (r : Result) : Sym.Simp.SimpM Result := do
  if let .step .. := r then bump env f
  return r

/-- With `debug`, records the last rewrite steps (kind, input head, output head). -/
def note (env : Env) (kind : String) (e : Expr) (r : Result) : Sym.Simp.SimpM Result := do
  if env.debug then
    if let .step e' .. := r then
      env.log.modify fun l =>
        let l := if l.size > 60 then l.extract 1 l.size else l
        l.push m!"{kind}: {e.getAppFn} [{e.getAppNumArgs}] ==> {e'.getAppFn} [{e'.getAppNumArgs}]"
  return r

def traced (env : Env) (kind : String) (s : Simproc) : Simproc := fun e => do
  if env.deadline > 0 then
    if (← IO.monoMsNow) > env.deadline then throwError "wide_symex_sym: time budget exhausted"
  let t0 ← IO.monoNanosNow
  let r ← s e
  let t1 ← IO.monoNanosNow
  env.kindMs.modify fun m => m.insert kind (m.getD kind 0 + (t1 - t0))
  note env kind e r

/-- Unfold a gated application with its equation theorems, else its unfold equation. -/
def unfoldStep (env : Env) : Simproc := fun e => do
  let fn := e.getAppFn
  let .const c us := fn | return .rfl
  unless ← gate env c do return .rfl
  if e.isConst then
    -- A constant (`coreLit`, `fuel`): delta, as `addDeclToUnfold` does for a nullary definition.
    let some ci := (← getEnv).find? c | return .rfl
    unless ci.hasValue && ci.levelParams.length == us.length do return .rfl
    let v ← instantiateValueLevelParams ci us
    let v ← Sym.shareCommon (← Sym.unfoldReducible v)
    bump env fun s => { s with deltaRw := s.deltaRw + 1 }
    return .step v (← Sym.mkEqRefl v)
  let thms ← Tactic.Cbv.getEqnTheorems c
  let r ← Simproc.tryCatch (thms.rewrite (d := dischargeNone)) e
  if let .step .. := r then
    bump env fun s => { s with eqnRw := s.eqnRw + 1 }
    return r
  if ← isRecLike c then return .rfl
  let some thm ← Tactic.Cbv.getUnfoldTheorem c | return .rfl
  let r ← Simproc.tryCatch (fun e => thm.rewrite e) e
  countStep env (fun s => { s with unfoldRw := s.unfoldRw + 1 }) r

/-- A projection function applied to a constructor application. -/
def projStep (env : Env) : Simproc := fun e => do
  let .const c _ := e.getAppFn | return .rfl
  let some info ← getProjectionFnInfo? c | return .rfl
  let args := e.getAppArgs
  unless args.size > info.numParams do return .rfl
  let s := args[info.numParams]!
  let .const k _ := s.getAppFn | return .rfl
  let some (.ctorInfo ki) := (← getEnv).find? k | return .rfl
  let sargs := s.getAppArgs
  unless sargs.size == ki.numParams + ki.numFields do return .rfl
  let v := mkAppN sargs[ki.numParams + info.i]! (args.extract (info.numParams + 1) args.size)
  let v ← Sym.shareCommon v.headBeta
  bump env fun s => { s with projRw := s.projRw + 1 }
  return .step v (← Sym.mkEqRefl v)

/-- A kernel projection (from an unfolded definition's body): fold it into a projection
function application, which `Sym.simp` handles. -/
def projFoldStep : Simproc := fun e => do
  unless e.isProj do return .rfl
  let e' ← Sym.shareCommon (← Sym.foldProjs e)
  if isSameExpr e e' then
    let some r ← reduceProj? e | return .rfl
    let r ← Sym.shareCommon r
    return .step r (← Sym.mkEqRefl r)
  return .step e' (← Sym.mkEqRefl e')

/-- `zeta := true` of `Meta.simp`: substitute `let`/`have` values. -/
def zetaStep (env : Env) : Simproc := fun e => do
  let .letE _ _ v b _ := e | return .rfl
  let v ← Sym.shareCommon (b.instantiate1 v)
  bump env fun s => { s with zetaRw := s.zetaRw + 1 }
  return .step v (← Sym.mkEqRefl v)

def betaStep (env : Env) : Simproc := fun e => do
  unless e.isApp && e.getAppFn.isLambda do return .rfl
  let v ← Sym.shareCommon e.headBeta
  bump env fun s => { s with betaRw := s.betaRw + 1 }
  return .step v (← Sym.mkEqRefl v)

/-- The default `@[simp]` set, reached through the Meta discrimination tree. -/
def bridgeStep (env : Env) : Simproc := fun e => do
  unless env.bridge do return .rfl
  unless e.isApp do return .rfl
  let cands ← try env.simpThms.post.getMatchWithExtra e catch _ => pure #[]
  for (thm, _) in cands do
    let .decl n .. := thm.origin | continue
    if (← env.bridgeMemo.get).contains n then continue
    let ok ← try
        let t ← mkTheoremFromDecl n
        env.bridgeSet.modify (·.insert t)
        pure true
      catch _ => pure false
    env.bridgeMemo.modify (·.insert n ok)
    bump env fun s => if ok then { s with bridgeConverted := s.bridgeConverted + 1 }
      else { s with bridgeConvFail := s.bridgeConvFail + 1 }
  let set ← env.bridgeSet.get
  let r ← Simproc.tryCatch (set.rewrite (d := dischargeSimpSelf)) e
  countStep env (fun s => { s with bridgeRw := s.bridgeRw + 1 }) r

/-- `decide := true` for closed propositions. -/
def decideStep (env : Env) : Simproc := fun e => do
  unless env.decide do return .rfl
  if e.hasFVar || e.hasMVar then return .rfl
  if (← Sym.isTrueExpr e) || (← Sym.isFalseExpr e) then return .rfl
  unless (← isProp e) do return .rfl
  let some inst ← (try synthInstance? (mkApp (mkConst ``Decidable) e) catch _ => pure none)
    | return .rfl
  let d := mkApp2 (mkConst ``Decidable.decide) e inst
  -- Bounded: an evaluation that does not finish within the budget leaves the proposition.
  let hb ← IO.getNumHeartbeats
  let r ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000 * 1000, initHeartbeats := hb })
      (withAtLeastTransparency .default <| whnf d))
    (fun _ => pure d)
  if r.isConstOf ``Bool.true then
    let h := mkApp3 (mkConst ``of_decide_eq_true) e inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    bump env fun s => { s with decideRw := s.decideRw + 1 }
    return .step (← Sym.getTrueExpr) (mkApp2 (mkConst ``eq_true) e h) (done := true)
  else if r.isConstOf ``Bool.false then
    let h := mkApp3 (mkConst ``of_decide_eq_false) e inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
    bump env fun s => { s with decideRw := s.decideRw + 1 }
    return .step (← Sym.getFalseExpr) (mkApp2 (mkConst ``eq_false) e h) (done := true)
  return .rfl

/-- `ite`/`dite`/`cond` and matchers: simplify only conditions and discriminants, and do not
enter the branches of one that stays stuck. -/
def controlStep : Simproc := fun e => do
  let .const c _ := e.getAppFn | return .rfl
  if c == ``ite || c == ``dite || c == ``cond then
    simpControl e
  else if let some info ← getMatcherInfo? c then
    -- Discriminants, then the matcher's equation theorems (syntactic, on constructor
    -- discriminants). Not `Cbv.tryMatcher`'s `reduceRecMatcher` fallback: it runs `whnf` at
    -- default transparency on the discriminants, which on run_f evaluated a symbolic byte list
    -- until the heartbeat cap.
    let start := info.numParams + 1
    let r ← simpAppArgRange e start (start + info.numDiscrs)
    match r with
    | .step .. => return r
    | .rfl _ cd =>
      let thms ← Tactic.Cbv.getMatchTheorems c
      match ← Simproc.tryCatch (thms.rewrite (d := dischargeNone)) e with
      | .rfl _ cd' => return .rfl true (cd || cd')
      | r => return r
  else return .rfl

def mkMethods (env : Env) (hyps : Theorems) : Methods :=
  { pre := Tactic.Cbv.isBuiltinValue <|> Tactic.Cbv.isProofTerm <|> traced env "kproj" projFoldStep <|> traced env "zeta" (zetaStep env) <|> traced env "control" controlStep
    post := traced env "ground" (evalGround { maxExponent := 512 })
      <|> traced env "lemma" (fun e => do countStep env (fun s => { s with lemmaRw := s.lemmaRw + 1 }) (← env.userThms.rewrite (d := dischargeSimpSelf) e))
      <|> traced env "hyp" (fun e => do countStep env (fun s => { s with hypRw := s.hypRw + 1 }) (← hyps.rewrite (d := dischargeSimpSelf) e))
      <|> traced env "proj" (projStep env) <|> traced env "beta" (betaStep env)
      <|> traced env "unfold" (unfoldStep env) <|> traced env "bridge" (bridgeStep env)
      <|> traced env "decide" (decideStep env) }

/-! ## Cache invalidation on a change of hypotheses -/

/-- Whether `e` contains (by pointer) one of `targets`, or one of the free variables `fvars`. -/
partial def mentions (targets : Std.HashSet ExprPtr) (fvars : FVarIdSet) (e : Expr) :
    StateM (Std.HashMap ExprPtr Bool) Bool := do
  if targets.contains { expr := e } then return true
  if let some b := (← get)[({ expr := e } : ExprPtr)]? then return b
  let b ← match e with
    | .fvar f => pure (fvars.contains f)
    | .app f a => do pure ((← mentions targets fvars f) || (← mentions targets fvars a))
    | .lam _ t b _ | .forallE _ t b _ => do
      pure ((← mentions targets fvars t) || (← mentions targets fvars b))
    | .letE _ t v b _ => do
      pure ((← mentions targets fvars t) || (← mentions targets fvars v) || (← mentions targets fvars b))
    | .mdata _ b | .proj _ _ b => mentions targets fvars b
    | _ => pure false
  modify (·.insert { expr := e } b)
  return b

def filterCache (c : Sym.Simp.Cache) (targets : Std.HashSet ExprPtr) (fvars : FVarIdSet) :
    Sym.Simp.Cache × Nat × Nat := Id.run do
  let mut memo : Std.HashMap ExprPtr Bool := {}
  let mut out : Sym.Simp.Cache := {}
  let mut kept := 0
  let mut dropped := 0
  for (k, r) in c.toList do
    let act : StateM (Std.HashMap ExprPtr Bool) Bool := do
      if ← mentions targets fvars k.expr then return true
      match r with
      | .rfl .. => return false
      | .step e' h .. => return (← mentions targets fvars e') || (← mentions targets fvars h)
    let (hit, m) := act.run memo
    memo := m
    if hit then dropped := dropped + 1 else
      kept := kept + 1
      out := out.insert k r
  return (out, kept, dropped)

/-- The left-hand side `Sym.simp` rewrites with a hypothesis of type `t`, when it is ground. -/
def hypLhs (t : Expr) : Option Expr :=
  if t.isForall then none else
  match t.eq? with
  | some (_, l, _) => some l
  | none => match t.not? with
    | some p => some p
    | none => match t.iff? with
      | some (l, _) => some l
      | none => some t

/-- The goal's hypotheses as rewrite rules, and the cache adjusted to them. -/
def prepareHyps (env : Env) (g : MVarId) : MetaM Theorems := g.withContext do
  let mut thms : Theorems := {}
  let mut hyps : Array (FVarId × Option Expr) := #[]
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    unless ← isProp h.type do continue
    try
      thms := thms.insert (← mkTheoremFromExpr h.toExpr)
      let l ← runSym env ((hypLhs h.type).mapM Sym.shareCommon)
      hyps := hyps.push (h.fvarId, l)
    catch _ => pure ()
  let s ← env.session.get
  if !env.share then
    -- No sharing across goals: every goal starts from an empty cache.
    env.session.modify fun s => { s with simpState := {}, cacheHyps := hyps }
    return thms
  let old := s.cacheHyps
  let added := hyps.filter fun (f, _) => !old.any (·.1 == f)
  let removed := old.filter fun (f, _) => !hyps.any (·.1 == f)
  unless added.isEmpty && removed.isEmpty do
    let t0 ← IO.monoMsNow
    let changed := added ++ removed
    if changed.any (·.2.isNone) then
      let n := s.simpState.persistentCache.foldl (fun n _ _ => n + 1) 0
      bump env fun c => { c with cacheResets := c.cacheResets + 1, cacheDropped := c.cacheDropped + n }
      env.session.modify fun s => { s with simpState := {}, cacheHyps := hyps }
    else
      let targets : Std.HashSet ExprPtr := changed.foldl (init := {}) fun acc (_, l) =>
        match l with | some l => acc.insert { expr := l } | none => acc
      let fvars : FVarIdSet := removed.foldl (init := {}) fun acc (f, _) => acc.insert f
      let (c, kept, dropped) := filterCache s.simpState.persistentCache targets fvars
      bump env fun st => { st with cacheKept := st.cacheKept + kept, cacheDropped := st.cacheDropped + dropped }
      env.session.modify fun s =>
        { s with simpState := { s.simpState with persistentCache := c }, cacheHyps := hyps }
    let t1 ← IO.monoMsNow
    bump env fun c => { c with invalidateMs := c.invalidateMs + (t1 - t0) }
  return thms

/-! ## The evaluator -/

/-- Sym rounds on `g` to a fixed point; `none` when it closes the goal. -/
def symEvalGoal (env : Env) (g : MVarId) : MetaM (Option MVarId) := do
  bump env fun c => { c with goals := c.goals + 1 }
  let t0 ← IO.monoMsNow
  let mut g ← runSym env (Sym.preprocessMVar g)
  let hyps ← prepareHyps env g
  let methods := mkMethods env hyps
  let mut result := some g
  for _ in [0:400] do
    bump env fun c => { c with symRounds := c.symRounds + 1 }
    let s ← env.session.get
    let g0 := g
    -- A heartbeat cap per Sym.simp call (`checkSystem` runs every 1000 steps), so a run that
    -- does not converge falls back to the Meta loop instead of hanging (symHeartbeats).
    let hb ← IO.getNumHeartbeats
    let r ← tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 400000 * 1000, initHeartbeats := hb }) <|
         some <$> runSym env (g0.withContext do
          let (r, st) ← Sym.Simp.SimpM.run (Sym.Simp.simp (← g0.getType)) methods
            { maxSteps := env.maxSteps, maxDischargeDepth := 4 } s.simpState
          let gr ← r.toSimpGoalResult g0
          return (gr, st)))
      fun ex => do
        logInfo m!"wide_symex_sym: Sym.simp failed: {ex.toMessageData}"
        if env.debug then logInfo m!"last steps:{indentD (MessageData.joinSep (← env.log.get).toList Format.line)}"
        bump env fun c => { c with symErrors := c.symErrors + 1 }
        pure none
    let some (gr, st) := r | break
    env.session.modify fun s => { s with simpState := st }
    bump env fun c => { c with symSteps := c.symSteps + st.numSteps }
    match gr with
    | .closed =>
      bump env fun c => { c with symProgressRounds := c.symProgressRounds + 1, symClosed := c.symClosed + 1 }
      result := none; break
    | .noProgress => result := some g; break
    | .goal g' =>
      bump env fun c => { c with symProgressRounds := c.symProgressRounds + 1 }
      g := g'; result := some g'
  let t1 ← IO.monoMsNow
  bump env fun c => { c with symMs := c.symMs + (t1 - t0) }
  return result

/-- Sym, then the existing `Meta.simp` loop on what is left (counting its progressing rounds). -/
def evalGoalSym (env : Env) (base : SimpTheorems) (g : MVarId) : TacticM (Option MVarId) := do
  let some g ← symEvalGoal env g | return none
  unless env.fallback do return some g
  let t0 ← IO.monoMsNow
  -- The same loop as `Wide.evalGoal`, counting the rounds that change the goal.
  let mut thms := base
  let mut done : NameSet := {}
  let mut g := g
  let mut rounds := 0
  let mut out := some g
  for _ in [0:400] do
    let names ← unfoldableIn (← instantiateMVars (← g.getType))
    for n in names.toList do
      unless done.contains n do
        done := done.insert n
        thms ← tryCatchRuntimeEx (thms.addDeclToUnfold n) (fun _ => pure thms)
    let thms' := thms
    let (r, _) ← g.withContext do
      let mut thmsH := thms'
      for h in (← getLCtx) do
        if !h.isImplementationDetail && (← isProp h.type) then
          thmsH ← thmsH.add (.fvar h.fvarId) #[] h.toExpr
      let ctx ← Simp.mkContext
        (config := { decide := true, maxSteps := 100000000, maxDischargeDepth := 4 })
        (simpTheorems := #[thmsH]) (congrTheorems := ← getSimpCongrTheorems)
      try simpGoal g ctx (simprocs := #[← Simp.getSimprocs])
      catch _ => pure (some (#[], g), {})
    match r with
    | none => rounds := rounds + 1; out := none; break
    | some (_, g') =>
      if g' == g then out := some g; break
      rounds := rounds + 1
      g := g'; out := some g'
  let t1 ← IO.monoMsNow
  bump env fun c => { c with fallbackMs := c.fallbackMs + (t1 - t0), fallbackRounds := c.fallbackRounds + rounds }
  bump env fun c => { c with fallbackGoals := c.fallbackGoals + (if rounds > 0 then 1 else 0) }
  bump env fun c => { c with fallbackClosed := c.fallbackClosed + (if out.isNone then 1 else 0) }
  return out

/-- `symexGoal` of `Wide.Tactic` with `evalGoalSym`. -/
partial def symexGoalSym (env : Env) (base : SimpTheorems) (depth : Nat) (g : MVarId) :
    TacticM (List MVarId) := do
  match ← evalGoalSym env base g with
  | none => return []
  | some g =>
    if depth = 0 then return [g]
    let ty ← g.withContext do instantiateMVars (← g.getType)
    let split? ← try
        some <$> (do
          setGoals [g]
          match closedCond? ty with
          | some c =>
            -- On the condition itself (not re-elaborated syntax), so that the new hypothesis is
            -- pointer-equal to the condition after sharing and the cache invalidation finds it.
            let (gt, gf) ← g.byCases c `hpath
            setGoals [gt.mvarId, gf.mvarId]
          | none => evalTactic (← `(tactic| split))
          getGoals)
      catch _ => pure none
    match split? with
    | none => return [g]
    | some gs =>
      bump env fun c => { c with splits := c.splits + 1 }
      let mut out := []
      for g' in gs do
        let closed ← try
            setGoals [g']
            evalTactic (← `(tactic| (exfalso; omega)))
            pure true
          catch _ => pure false
        if closed then bump env fun c => { c with omegaClosed := c.omegaClosed + 1 }
        unless closed do
          out := out ++ (← symexGoalSym env base (depth - 1) g')
      return out

/-- The user lemmas as `Sym` theorems; definitions named among them are unfolded instead. -/
def userTheorems (ts : Array Syntax) : TacticM (Theorems × NameSet) := do
  let mut thms : Theorems := {}
  let mut unf : NameSet := {}
  for n in monadLemmas ++ wordLemmas ++ [``eq_self_iff_true] do
    try thms := thms.insert (← mkTheoremFromDecl n) catch _ => pure ()
  for t in ts do
    if t.isIdent then
      if ((← getLCtx).findFromUserName? t.getId).isSome then continue  -- a hypothesis
      if let some n ← (try some <$> realizeGlobalConstNoOverload t catch _ => pure none) then
        if ((← getEnv).find? n).any ConstantInfo.isDefinition then
          unf := unf.insert n
          continue
        try thms := thms.insert (← mkTheoremFromDecl n) catch _ => pure ()
        continue
    try thms := thms.insert (← mkTheoremFromExpr (← elabTerm t none)) catch _ => pure ()
  return (thms, unf)

def mkEnv (ts : Array Syntax) (bridge fallback share debug decide : Bool) (budgetMs : Nat := 0) : TacticM Env := do
  let (symCtx, symState) ← Sym.SymM.run do return (← read, ← get)
  let now ← IO.monoMsNow
  let (userThms, userUnfold) ← (← getMainGoal).withContext (userTheorems ts)
  return { counters := ← IO.mkRef {}, session := ← IO.mkRef { symCtx, symState }
           gateMemo := ← IO.mkRef {}, bridgeMemo := ← IO.mkRef {}, bridgeSet := ← IO.mkRef {}
           userUnfold, userThms, simpThms := ← getSimpTheorems, bridge, fallback, share,
           maxSteps := 300000, debug, decide,
           deadline := if budgetMs == 0 then 0 else now + budgetMs, log := ← IO.mkRef #[], kindMs := ← IO.mkRef {} }

def report (env : Env) : TacticM Unit := do
  let s ← env.session.get
  env.counters.modify fun c => { c with cacheFinal := s.simpState.persistentCache.foldl (fun n _ _ => n + 1) 0 }
  let c ← env.counters.get
  logInfo m!"wide_symex_sym counters: {repr c}"
  let ks := (← env.kindMs.get).toList.map fun (k, v) => s!"{k}={v / 1000000}ms"
  logInfo m!"wide_symex_sym simproc time: {ks}"

declare_syntax_cat symexOpt (behavior := symbol)
syntax &"nobridge" : symexOpt
syntax &"nofallback" : symexOpt
syntax &"noshare" : symexOpt
syntax &"debug" : symexOpt
syntax &"nodecide" : symexOpt
syntax &"withdecide" : symexOpt
syntax &"budget60" : symexOpt

def runSymex (opts : Array Syntax) (ts : Array Syntax) (lemmas : Array Syntax) : TacticM Unit := do
  let has (s : String) : Bool := opts.any fun o => o[0].getAtomVal == s
  let env ← mkEnv (lemmas ++ ts) (!has "nobridge") (!has "nofallback") (!has "noshare") (has "debug") (has "withdecide") (if has "budget60" then 60000 else 0)
  let base ← baseTheorems (lemmas ++ ts)
  let rest := (← getGoals).drop 1
  let gs ← symexGoalSym env base 16 (← getMainGoal)
  setGoals (gs ++ rest)
  report env

/-- Symbolic evaluation of SolidCore's interpreter with path splitting, on `Sym.simp`. -/
syntax "src_symex_sym" symexOpt* (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| src_symex_sym $os* $[[$ts,*]]?) =>
    runSymex (os.map (·.raw)) (ts.map (·.getElems.map (·.raw)) |>.getD #[]) #[]

/-- `wide_symex` on `Sym.simp`: the rewrite rules of a call of a wide function and `src_symex_sym`. -/
syntax "wide_symex_sym" symexOpt* " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| wide_symex_sym $os* [$ts,*]) => do
    let lemmas := #[``SolidCore.Refinement.Dirty.readSelector_calldata, ``drop_selector, ``readWord_argBytes',
      ``wordToBytesBE_eq, ``SolidCore.Refinement.Dirty.length_argBytes, ``addWord_eq, ``subWord_eq, ``mulWord_eq,
      ``xorWord_eq, ``andWord_eq, ``orWord_eq, ``ltWord_eq, ``gtWord_eq, ``BitVec.ofNat_toNat,
      ``BitVec.setWidth_eq].map fun n => (mkIdent n).raw
    runSymex (os.map (·.raw)) (ts.getElems.map (·.raw)) lemmas

end Verify.Eval.B
