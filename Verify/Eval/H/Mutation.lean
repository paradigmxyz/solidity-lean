import Lean

/-!
# Mutation harness (lane H)

    #mutation_check "name" : orig_stmt
      rejects [ "label₁" => mutant₁, "label₂" => mutant₂ ]
      using tac

runs the tactic script `tac` on the original statement and on every mutant, each from a fresh
goal. The check passes only when

* the original closes with no goals left, no error logged, no `sorry`, no metavariable, and the
  kernel accepts the proof (it is added under the declaration name `name`, so later audits see
  it); and
* every mutant is rejected: the tactic throws, logs an error, leaves goals, produces `sorry` or a
  metavariable, or the kernel refuses the term.

A mutant that goes through is reported as `MUTANT SURVIVED` and fails the file. Each mutant runs
on a saved state that is restored afterwards, messages included, so a failing mutant leaves
nothing behind (the original keeps its auxiliary declarations, which its proof uses). The same script runs on every statement, so a mutant that survives shows the
engine (or the statement) is too weak, not a different proof.

`#mutation_check_engine "name" : stmt using tac` only runs the original (for engines whose
mutants are listed in a separate check).
-/

namespace Verify.Eval.H

open Lean Elab Command Term Meta

/-- What happened when the script ran on one statement. -/
inductive Verdict where
  | proved (proof : Expr)
  | rejected (why : String)

/-- Runs `tac` on `type` from a fresh goal; `proved` only if the result is a closed term that the
kernel accepts as a theorem of `type`. Restores the state (and message log) afterwards. -/
def runScript (type : Expr) (tac : Syntax) (lparams : List Name) (keep := false) : TermElabM Verdict := do
  let s ← saveState
  let msgs ← Core.getMessageLog
  Core.resetMessageLog
  let v ← try
      let mvar ← mkFreshExprSyntheticOpaqueMVar type
      let gs ← withoutErrToSorry <| Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
      synthesizeSyntheticMVarsNoPostponing
      let log ← Core.getMessageLog
      if log.hasErrors then
        pure (Verdict.rejected s!"error logged: {((← (log.toList.filter (·.severity == .error)).getLast!.toString).take 160)}")
      else if !gs.isEmpty then
        pure (.rejected s!"{gs.length} goal(s) left")
      else
        let pf ← instantiateMVars mvar
        if pf.hasMVar then pure (.rejected "proof has metavariables")
        else if pf.hasSyntheticSorry || pf.hasSorry then pure (.rejected "proof uses sorry")
        else
          let decl := Declaration.thmDecl
            (mkTheoremValEx (Name.mkSimple "_mutation_probe") lparams type pf [])
          match (← getEnv).toKernelEnv.addDeclCore 0 100000000 decl none with
          | .ok _ => pure (.proved pf)
          | .error e => pure (.rejected s!"kernel: {((← (e.toMessageData (← getOptions)).toString).take 160)}")
    catch e =>
      pure (.rejected s!"exception: {((← e.toMessageData.toString).take 160)}")
  match keep, v with
  | true, .proved _ => Core.setMessageLog msgs
  | _, _ => s.restore; Core.setMessageLog msgs
  return v

/-- Elaborates a closed statement (universe parameters become the declaration's). -/
def elabStmt (stx : Term) : TermElabM (Expr × List Name) := do
  let e ← elabType stx
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← levelMVarToParam e
  let e ← instantiateMVars e
  if e.hasMVar then throwError "statement {e} has metavariables"
  let lps := (collectLevelParams {} e).params.toList
  return (e, lps)

syntax (name := mutationCheck) "#mutation_check " str " : " term
  " rejects " "[" (str " => " term),* "]" " using " tacticSeq : command

syntax (name := mutationEngine) "#mutation_check_engine " str " : " term " using " tacticSeq : command

def checkOriginal (name : String) (orig : Term) (tac : Syntax) : CommandElabM Unit :=
  liftTermElabM do
    let (ty, lps) ← elabStmt orig
    match ← runScript ty tac lps (keep := true) with
    | .rejected why => throwError "mutation {name}: ORIGINAL NOT PROVED by the script ({why})"
    | .proved pf =>
      addDecl (Declaration.thmDecl (mkTheoremValEx (Name.mkSimple name) lps ty pf []))

elab_rules : command
  | `(#mutation_check_engine $name:str : $orig:term using $tac:tacticSeq) =>
    checkOriginal name.getString orig tac
  | `(#mutation_check $name:str : $orig:term rejects [ $[$labels:str => $mutants:term],* ] using $tac:tacticSeq) => do
    checkOriginal name.getString orig tac
    let mut lines := #[]
    let mut survived := #[]
    for l in labels, m in mutants do
      let v ← liftTermElabM do
        let (ty, lps) ← elabStmt m
        runScript ty tac lps
      match v with
      | .proved _ =>
        survived := survived.push l.getString
        lines := lines.push s!"  {l.getString}: SURVIVED"
      | .rejected why => lines := lines.push s!"  {l.getString}: rejected ({why})"
    let summary := s!"mutation {name.getString}: original proved; {labels.size - survived.size}/{labels.size} mutants rejected\n" ++
      "\n".intercalate lines.toList
    if survived.isEmpty then logInfo summary
    else throwError "MUTANT SURVIVED in {name.getString}: {survived}\n{summary}"

end Verify.Eval.H
