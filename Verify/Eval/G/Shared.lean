import Lean

/-!
# Lane G: one shared fact context for many arithmetic side conditions

g_simp [rw1, ...] using [t1, ...] rewrites the main goal with the conditional rewrite lemmas
rw_i (through Sym.simp), and proves every side condition those lemmas raise with grind from ONE
internalized copy of the goal's hypotheses:

1. the goal becomes a Grind.Goal (Grind.mkGoal) and its whole local context, the path
   conditions and word facts of the branch, is internalized once (Goal.internalizeAll) into
   grind's E-graph and its linear-arithmetic solver;
2. the trigger lemmas t_i are the only E-matching theorems (Grind.mkOnlyParams, so no
   @[grind] set is active) and are activated once on that goal;
3. Goal.mkSymSimpDischarger turns that goal into a Sym.simp discharger: each side condition
   starts from the shared state, internalizes only what it adds (its negation), runs grind,
   and its own solver state is dropped afterwards.

Nothing outlives one g_simp call: the Grind.Goal and the Sym.simp cache live inside one
GrindM.run. g_split_simp c [..] using [..] shows the branch discipline: it internalizes the
parent's facts once, splits on c (MVarId.byCases), internalizes only the branch's new
hypothesis into each child (a persistent copy of the parent's state), and rewrites each child
with its own discharger. g_split_simp_shared additionally keeps ONE Sym.simp cache across
both children, positive first, to show that the cache does not carry a branch-local discharge
into the sibling (every grind discharge is marked context dependent). g_split_simp_leaky is a
deliberately wrong control that discharges the negative child's side conditions from the
POSITIVE child's goal: the sibling-isolation tests (Tests.lean) must reject it.

Proofs are ordinary terms (grind's and Sym.simp's): the kernel checks them; no native_decide,
no bv_decide.
-/

namespace Verify.Eval.G

open Lean Meta Elab Tactic
open Lean.Meta.Grind (Goal)

/-- grind's configuration for side conditions: no global lemma set (the caller passes the
trigger lemmas), a bounded number of instances and few case splits. -/
def sideConfig : Grind.Config :=
  { splits := 4, instances := 200, gen := 4, ematch := 3, lookahead := false, verbose := false }

/-- The Sym.simp theorems of the rewrite lemmas. -/
def rwTheorems (rw : Array Name) : MetaM Sym.Simp.Theorems := do
  let mut thms : Sym.Simp.Theorems := {}
  for n in rw do
    for t in ← Sym.Simp.mkTheoremsFromDecl n do
      thms := thms.insert t
  return thms

/-- grind's parameters: only the trigger lemmas as E-matching theorems. -/
def sideParams (trig : Array Name) (cfg : Grind.Config := sideConfig) : MetaM Grind.Params := do
  let mut params ← Grind.mkOnlyParams cfg
  for n in trig do
    let t ← Grind.mkEMatchTheoremForDecl n (.default false) params.symPrios
    params := { params with extra := params.extra.push t }
  return params

/-- Counters of one run: side conditions tried and proved. -/
structure Stats where
  tried : Nat := 0
  proved : Nat := 0
  deriving Inhabited

/-- Wraps a discharger to count its attempts. -/
def counting (ref : IO.Ref Stats) (d : Sym.Simp.Discharger) : Sym.Simp.Discharger := fun e => do
  let r ← d e
  let ok := match r with | .solved .. => 1 | .failed .. => 0
  ref.modify fun s => { s with tried := s.tried + 1, proved := s.proved + ok }
  return r

/-! ## The shared facts and their discharger

A shared fact state is a Grind.Goal over a fresh goal False in the context, internalized once.
When the context itself is contradictory, grind closes that goal False while internalizing (it
assigns the goal it holds) and marks the state inconsistent. Lean's Goal.dischargeSymSimp then
reports every later side condition as solved but leaves its proof, a fresh metavariable,
unassigned, since solve sees the inherited inconsistency and assigns nothing (pinned
src/Lean/Meta/Sym/Grind.lean and Grind/Types.lean closeGoal). Facts records the proof of False
instead, and the discharger answers False.elim of it, a closed term. -/

structure Facts where
  goal : Goal
  /-- A proof of False from the context, when grind found it contradictory. -/
  falsePf? : Option Expr := none

def falseExpr : Expr := mkConst (Name.mkSimple "False")

/-- The proof of False grind left in fm, if the state is inconsistent. -/
def falseOf (g : Goal) (fm : Expr) : MetaM (Option Expr) := do
  unless g.inconsistent do return none
  let p ← instantiateMVars fm
  if p.hasExprMVar then throwError "g_simp: grind marked the facts inconsistent but left no proof of False"
  return some p

/-- The facts of mvarId's context: extending parent (whose context must be a prefix) by the
declarations it lacks, or from scratch. Each call works on its own copy: parent is unchanged. -/
def factsAt (params : Grind.Params) (parent : Option Facts) (mvarId : MVarId) : Grind.GrindM Facts := do
  let fm ← mvarId.withContext (mkFreshExprSyntheticOpaqueMVar falseExpr)
  match parent with
  | some p =>
    if p.falsePf?.isSome then return { p with goal := { p.goal with mvarId := fm.mvarId! } }
    let g ← ({ p.goal with mvarId := fm.mvarId! } : Goal).internalizeAll
    return { goal := g, falsePf? := ← falseOf g fm }
  | none =>
    let g ← Grind.mkGoal fm.mvarId!
    let g ← Grind.GoalM.run' g (Grind.assertExtra params)
    let g ← g.internalizeAll
    return { goal := g, falsePf? := ← falseOf g fm }

/-- The discharger of a fact state: Goal.mkSymSimpDischarger, or False.elim when contradictory. -/
def Facts.discharger (f : Facts) : Grind.GrindM Sym.Simp.Discharger := do
  let d ← f.goal.mkSymSimpDischarger
  return fun e => match f.falsePf? with
    | some p => return .solved (mkApp2 (mkConst (Name.mkStr2 "False" "elim") [Level.zero]) e p) true
    | none => d e

/-- Rewrites goal with thms, discharging side conditions from facts (whose context is a prefix of
goal's). -/
def simpWith (goal : MVarId) (facts : Facts) (thms : Sym.Simp.Theorems) (ref : IO.Ref Stats)
    (cache : Sym.Simp.State := {}) : Grind.GrindM (Option MVarId × Sym.Simp.State) := do
  let d := counting ref (← facts.discharger)
  let methods : Sym.Simp.Methods := { post := thms.rewrite d }
  let goal ← Sym.preprocessMVar goal
  let (r, cache) ← goal.withContext do
    Sym.Simp.SimpM.run (Sym.Simp.simp (← goal.getType)) methods {} cache
  -- In the goal's context: the new goal must keep the branch's hypotheses.
  match ← goal.withContext (Sym.Simp.Result.toSimpGoalResult r goal) with
  | .closed => return (none, cache)
  | .goal m => return (some m, cache)
  | .noProgress => return (some goal, cache)

/-- g_simp on one goal. -/
def gSimp (mvarId : MVarId) (rw trig : Array Name) : MetaM (Option MVarId × Stats) := do
  let thms ← rwTheorems rw
  let params ← sideParams trig
  let ref ← IO.mkRef ({} : Stats)
  let r ← Grind.GrindM.run (params := params) do
    let facts ← factsAt params none mvarId
    let (r, _) ← simpWith mvarId facts thms ref
    return r
  return (r, ← ref.get)

syntax (name := gSimpStx) "g_simp" " [" ident,* "]" (" using" " [" ident,* "]")? : tactic

def resolveNames (ids : Array Syntax) : TacticM (Array Name) :=
  ids.mapM fun id => realizeGlobalConstNoOverloadWithInfo id

register_option g_simp.trace : Bool := { defValue := false, descr := "log g_simp's counters" }

@[tactic gSimpStx] def evalGSimp : Tactic := fun stx => withMainContext do
  let rw ← resolveNames stx[2].getSepArgs
  let trig ← if stx[4].isNone then pure #[] else resolveNames stx[4][2].getSepArgs
  let (r, s) ← gSimp (← getMainGoal) rw trig
  if g_simp.trace.get (← getOptions) then
    logInfo m!"g_simp: side conditions tried {s.tried}, proved {s.proved}"
  match r with
  | none => replaceMainGoal []
  | some m => replaceMainGoal [m]

/-- Splits mvarId on c and rewrites both children; see the module docs. leaky := true
discharges the negative child's side conditions from the positive child's goal (a wrong
control, for the isolation tests). -/
def gSplitSimp (mvarId : MVarId) (c : Expr) (rw trig : Array Name) (shareCache leaky : Bool) :
    MetaM (List MVarId × Stats) := do
  let thms ← rwTheorems rw
  let params ← sideParams trig
  let ref ← IO.mkRef ({} : Stats)
  let r ← Grind.GrindM.run (params := params) do
    -- The parent's facts, once.
    let root ← factsAt params none mvarId
    let (pos, neg) ← mvarId.byCases c (Name.mkSimple "h")
    -- Each child: a persistent copy of the parent's state plus its own new hypothesis.
    let fp ← factsAt params (some root) pos.mvarId
    let fn ← factsAt params (some root) neg.mvarId
    let (rp, cache) ← simpWith pos.mvarId fp thms ref
    let cache := if shareCache then cache else {}
    -- The leaky control discharges in the negative child from the positive child's facts.
    let (rn, _) ← simpWith neg.mvarId (if leaky then fp else fn) thms ref cache
    return [rp, rn].filterMap id
  return (r, ← ref.get)

syntax (name := gSplitSimpStx) "g_split_simp" term:max
  " [" ident,* "]" (" using" " [" ident,* "]")? : tactic
syntax (name := gSplitSimpSharedStx) "g_split_simp_shared" term:max
  " [" ident,* "]" (" using" " [" ident,* "]")? : tactic
syntax (name := gSplitSimpLeakyStx) "g_split_simp_leaky" term:max
  " [" ident,* "]" (" using" " [" ident,* "]")? : tactic

def evalSplitCore (cStx rwStx trigStx : Syntax) (share leaky : Bool) : TacticM Unit :=
  withMainContext do
  let c ← Term.elabTerm cStx (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let c ← instantiateMVars c
  let rw ← resolveNames rwStx.getSepArgs
  let trig ← if trigStx.isNone then pure #[] else resolveNames trigStx[2].getSepArgs
  let (gs, s) ← gSplitSimp (← getMainGoal) c rw trig share leaky
  if g_simp.trace.get (← getOptions) then
    logInfo m!"g_split_simp: side conditions tried {s.tried}, proved {s.proved}"
  replaceMainGoal gs

@[tactic gSplitSimpStx] def evalGSplitSimp : Tactic := fun stx =>
  evalSplitCore stx[1] stx[3] stx[5] false false

@[tactic gSplitSimpSharedStx] def evalGSplitSimpShared : Tactic := fun stx =>
  evalSplitCore stx[1] stx[3] stx[5] true false

@[tactic gSplitSimpLeakyStx] def evalGSplitSimpLeaky : Tactic := fun stx =>
  evalSplitCore stx[1] stx[3] stx[5] false true


/-! ## Facts collected once

g_facts [l1, ...] instantiates each equation l_i, ∀ xs, lhs = rhs, at every subterm of the goal
and of its hypotheses its left side matches (up to reducible unfolding, instances found by the same pattern match
E-matching would use), and adds each instance as a hypothesis, once. Run before g_simp, the side
conditions' terms (the offsets, say) then reach the grind state with their arithmetic already
known, so no E-matching is needed per side condition. -/

/-- The instances of lemma n at the subterms of e. -/
def factInstances (n : Name) (e : Expr) : MetaM (Array Expr) := do
  let thm ← mkConstWithFreshMVarLevels n
  let ty ← inferType thm
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let terms ← collectSubterms e
  for t in terms do
    if seen.contains t then continue
    let (xs, _, body) ← forallMetaTelescopeReducing ty
    let some (_, lhs, _) := body.eq? | throwError "g_facts: {n} is not an equation"
    if ← withReducible (isDefEq lhs t) then
      let p ← instantiateMVars (mkAppN thm xs)
      unless p.hasExprMVar do
        seen := seen.insert t
        out := out.push p
  return out
where
  collectSubterms (e : Expr) : MetaM (Array Expr) := do
    let r ← IO.mkRef (#[] : Array Expr)
    Meta.transform e (pre := fun x => do
      unless x.hasLooseBVars do r.modify (·.push x)
      return .continue) |> discard
    r.get

syntax (name := gFactsStx) "g_facts" " [" ident,* "]" : tactic

@[tactic gFactsStx] def evalGFacts : Tactic := fun stx => withMainContext do
  let lemmas ← resolveNames stx[2].getSepArgs
  let goal ← getMainGoal
  -- The goal and every hypothesis: path conditions mention the words too.
  let mut ty ← instantiateMVars (← goal.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← Meta.isProp d.type then ty := mkApp2 (mkConst ``And) ty (← instantiateMVars d.type)
  let mut g := goal
  let mut n := 0
  for l in lemmas do
    for p in ← factInstances l ty do
      let (_, g') ← (← g.assert (Name.mkSimple s!"gfact{n}") (← inferType p) p).intro1P
      g := g'
      n := n + 1
  if g_simp.trace.get (← getOptions) then logInfo m!"g_facts: {n} facts"
  replaceMainGoal [g]

/-! ## Timing -/

/-- g_time "label" in cmd: elaborates cmd (with Elab.async false, so the kernel check is
inside) and logs its wall time. -/
syntax (name := gTime) "g_time " str " in " command : command

open Command in
@[command_elab gTime] def elabGTime : CommandElab := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let t0 ← IO.monoNanosNow
  withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
    elabCommand stx[3]
  let t1 ← IO.monoNanosNow
  logInfo m!"g_time {label}: {(t1 - t0).toFloat / 1000000.0} ms"

end Verify.Eval.G
