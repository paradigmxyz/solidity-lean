import Verify.Eval.G.Shared

/-!
# Lane G: one context, many candidate side conditions, three dischargers

g_compare [p1, ..., pn] base tac using [t1, ...] runs, in the current goal's context:

- base: tac on a fresh goal for each p_i, one after another (as simp calls its discharger once per
  candidate rewrite), timing each attempt and keeping the proofs it finds;
- shared: ONE Grind.Goal for the context, internalized once (Goal.internalizeAll), with the
  trigger lemmas t_i as the only E-matching theorems, then Goal.mkSymSimpDischarger on each p_i;
- ground: p_i without free variables decided by decide (kernel evaluation of its Decidable
  instance, no context); every candidate decide does not prove goes to the shared discharger.
  instance, no context), else the shared discharger.

It logs per variant the attempts, the number proved, the elaboration time, and the kernel time of
the proofs found (each added to the kernel as a theorem over the context and timed), and warns
on every candidate where a variant and the base disagree, so that a speed-up is never bought by
proving something else. The goal itself is left unchanged.
-/

namespace Verify.Eval.G

open Lean Meta Elab Tactic

/-- Adds proof : type, closed over the context, to the kernel as a fresh theorem; returns the
kernel time in ns. -/
def kernelTime (type proof : Expr) : MetaM Nat := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  let lctx ← getLCtx
  let fvars := lctx.foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.toExpr
  let ty ← mkForallFVars fvars type
  let pf ← mkLambdaFVars fvars proof
  if pf.hasMVar || ty.hasMVar then
    throwError "g_compare: a proof of{indentExpr type}\nstill has metavariables after instantiateMVars:{indentExpr proof}"
  let name ← mkAuxDeclName (Name.mkSimple "gcmp")
  let decl := Declaration.thmDecl (mkTheoremValEx name [] ty pf [])
  -- Outside the timed region: toKernelEnv waits for the environment's pending asynchronous
  -- checks (earlier theorems), which would otherwise count as this proof's kernel time.
  let kenv := (← getEnv).toKernelEnv
  let t0 ← IO.monoNanosNow
  match kenv.addDeclCore 0 100000 decl none with
  | .ok _ => return (← IO.monoNanosNow) - t0
  | .error e => throwError "g_compare: the kernel rejected a proof: {e.toMessageData {}}"

syntax (name := gCompareStx) "g_compare" " [" term,* "]" " base " tactic (" using" " [" ident,* "]")? : tactic

def ms (n : Nat) : Float := n.toFloat / 1000000.0

def trueExpr : Expr := mkConst (Name.mkSimple "True")

/-- The shared discharger on each p (see the module docs); none where it fails. -/
def sharedRun (params : Grind.Params) (props : Array Expr) : MetaM (Array (Option Expr)) := do
  let target ← mkFreshExprSyntheticOpaqueMVar trueExpr
  Grind.GrindM.run (params := params) do
    let facts ← factsAt params none target.mvarId!
    let d ← facts.discharger
    let mut out := #[]
    for p in props do
      let (r, _) ← Sym.Simp.SimpM.run (d p)
      out := out.push (match r with | .solved pf _ => some pf | .failed _ => none)
    return out

@[tactic gCompareStx] def evalGCompare : Tactic := fun stx => withMainContext do
  let props ← stx[2].getSepArgs.mapM fun t => do
    let e ← Term.elabTerm t (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let baseTac := stx[5]
  let trig ← if stx[6].isNone then pure #[] else resolveNames stx[6][2].getSepArgs
  -- base
  let mut baseOk : Array Bool := #[]
  let mut baseNs := 0
  let mut baseK := 0
  for p in props do
    let m ← mkFreshExprSyntheticOpaqueMVar p
    let t0 ← IO.monoNanosNow
    let ok ← try
        let gs ← Tactic.run m.mvarId! (withoutRecover (evalTactic baseTac))
        pure (gs.isEmpty && !(← instantiateMVars m).hasSyntheticSorry)
      catch e =>
        if g_simp.trace.get (← getOptions) then logInfo m!"g_compare base failed: {e.toMessageData}"
        pure false
    baseNs := baseNs + ((← IO.monoNanosNow) - t0)
    if ok then baseK := baseK + (← kernelTime p m)
    baseOk := baseOk.push ok
  -- shared
  let params ← sideParams trig
  let t0 ← IO.monoNanosNow
  let sharedRes ← sharedRun params props
  let sharedNs := (← IO.monoNanosNow) - t0
  let mut sharedK := 0
  for (p, r) in props.zip sharedRes do
    if let some pf := r then sharedK := sharedK + (← kernelTime p pf)
  -- ground first
  let t1 ← IO.monoNanosNow
  let mut groundRes : Array (Option Expr) := #[]
  let mut rest : Array (Nat × Expr) := #[]
  for i in [0:props.size] do
    let p := props[i]!
    if p.hasFVar || p.hasMVar then
      groundRes := groundRes.push none
      rest := rest.push (i, p)
    else
      let pf? ← try
          let d ← mkDecide p
          let v ← withAtLeastTransparency .default <| whnf d
          if v.isConstOf (Name.mkStr2 "Bool" "true") then pure (some (← mkDecideProof p)) else pure none
        catch _ => pure none
      groundRes := groundRes.push pf?
      -- A closed candidate that does not evaluate to true may still follow from a contradictory
      -- path context: it goes to the shared discharger too.
      if pf?.isNone then rest := rest.push (i, p)
  if !rest.isEmpty then
    let r ← sharedRun params (rest.map (·.2))
    for ((i, _), pf) in rest.zip r do groundRes := groundRes.set! i pf
  let groundNs := (← IO.monoNanosNow) - t1
  let mut groundK := 0
  for (p, r) in props.zip groundRes do
    if let some pf := r then groundK := groundK + (← kernelTime p pf)
  let nb := (baseOk.filter id).size
  let ns := (sharedRes.filter Option.isSome).size
  let ng := (groundRes.filter Option.isSome).size
  logInfo m!"g_compare: {props.size} candidates; base proved {nb} in {ms baseNs} ms (kernel {ms baseK} ms); shared proved {ns} in {ms sharedNs} ms (kernel {ms sharedK} ms); ground+shared proved {ng} in {ms groundNs} ms (kernel {ms groundK} ms)"
  for i in [0:props.size] do
    let b := baseOk[i]!
    if b != sharedRes[i]!.isSome then
      logWarning m!"g_compare: base {b}, shared {sharedRes[i]!.isSome} on{indentExpr props[i]!}"
    if b != groundRes[i]!.isSome then
      logWarning m!"g_compare: base {b}, ground {groundRes[i]!.isSome} on{indentExpr props[i]!}"

end Verify.Eval.G
