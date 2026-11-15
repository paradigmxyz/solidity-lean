import Lean

/-!
# Expected statements (lane H)

A lane that re-proves a baseline theorem `foo_old` with a new engine writes `foo_new` and states,
separately from the proof, that it proves the same thing:

    #same_statement foo_new foo_old            -- types identical up to universe names
    #same_statement foo_new foo_old (defeq)    -- or definitionally equal at reducible transparency
    #expect_statement foo_new : Stmt           -- the type is exactly the elaborated `Stmt`
    #same_imports foo_new foo_old              -- both modules have the same imports
    #statement_hash foo_new                    -- a stable hash of the type, for the manifest

Each command fails (an error, so the file does not check) when the statements differ, and prints
the first place they differ. A tactic that closes a weaker goal (a dropped hypothesis turned
into a stronger one, a dropped conjunct, `<` turned into `≤`, a narrowed quantifier, a changed
constant) then cannot pass for the baseline, however the proof was found.

The default comparison is syntactic (`Expr.eqv` after renaming universe parameters by position,
with `mdata` stripped), which a different statement cannot pass. `(defeq)` admits statements that
unfold to each other with reducible definitions only, so an `abbrev` of the statement passes but a
`def` that hides a weaker one does not.
-/

namespace Verify.Eval.H

open Lean Elab Command Meta

/-- The type of `n` with universe parameters renamed `u_1, u_2, …` by position and `mdata` dropped. -/
def normalizedType (n : Name) : CoreM Expr := do
  let ci ← getConstInfo n
  let us := ci.levelParams.zipIdx.map fun (_, i) => Level.param (Name.mkSimple s!"u_{i+1}")
  return (ci.type.instantiateLevelParams ci.levelParams us).consumeMData

/-- The first subterm where `a` and `b` differ, for the error message. -/
partial def firstDiff (a b : Expr) : Expr × Expr :=
  match a, b with
  | .app f x, .app g y =>
    if f.eqv g then firstDiff x y else if x.eqv y then firstDiff f g else (a, b)
  | .forallE _ t c _, .forallE _ t' c' _ | .lam _ t c _, .lam _ t' c' _ =>
    if t.eqv t' then firstDiff c c' else firstDiff t t'
  | .mdata _ x, _ => firstDiff x b
  | _, .mdata _ y => firstDiff a y
  | _, _ => (a, b)

/-- A hash of the statement of `n` that is the same on every run of the same toolchain. -/
def statementHash (n : Name) : CoreM UInt64 := do
  return (← normalizedType n).hash

def checkSame (new old : Name) (defeq : Bool) : MetaM Unit := do
  let a ← normalizedType new
  let b ← normalizedType old
  let la := (← getConstInfo new).levelParams.length
  let lb := (← getConstInfo old).levelParams.length
  if la != lb then
    throwError "statement mismatch: {new} has {la} universe parameters, {old} has {lb}"
  if a.eqv b then return
  if defeq then
    if ← withReducible (isDefEq a b) then return
  let (x, y) := firstDiff a b
  throwError "statement mismatch: {new} does not state {old}\n  {new}: {a}\n  {old}: {b}\nfirst difference:\n  {x}\nvs\n  {y}"

syntax (name := sameStatement) "#same_statement " ident ppSpace ident (" (defeq)")? : command

@[command_elab sameStatement] def elabSameStatement : CommandElab := fun stx => do
  let new ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let old ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  liftTermElabM <| checkSame new old (!stx[3].isNone)
  logInfo m!"same_statement {new} {old}: ok (hash {← liftCoreM (statementHash new)})"

syntax (name := expectStatement) "#expect_statement " ident " : " term : command

@[command_elab expectStatement] def elabExpectStatement : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ci ← getConstInfo n
  liftTermElabM do
    -- elaborate the expected statement with the declaration's universe parameters in scope
    let e ← Term.withLevelNames ci.levelParams do
      let e ← Term.elabType stx[3]
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    if e.hasMVar then throwError "expected statement has metavariables: {e}"
    let t := ci.type.consumeMData
    unless t.eqv e.consumeMData do
      let (x, y) := firstDiff t e
      throwError "statement mismatch: {n} does not have the expected statement\n  actual:   {t}\n  expected: {e}\nfirst difference:\n  {x}\nvs\n  {y}"
  logInfo m!"expect_statement {n}: ok"

/-- The imports of the module that declares `n` (the current file's for a local declaration). -/
def importsOf (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  match env.getModuleIdxFor? n with
  | some idx => return env.header.moduleData[idx.toNat]!.imports.map (·.module)
  | none => return env.header.imports.map (·.module)

syntax (name := sameImports) "#same_imports " ident ppSpace ident : command

@[command_elab sameImports] def elabSameImports : CommandElab := fun stx => do
  let a ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let b ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let ia ← liftCoreM (importsOf a)
  let ib ← liftCoreM (importsOf b)
  let env ← getEnv
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.header.mainModule
  -- the new module may import the baseline's module itself; beyond that the imports must agree
  let sa := (ia.filter (· != modOf b)).qsort (·.toString < ·.toString)
  let sb := ib.qsort (·.toString < ·.toString)
  unless sa == sb do
    throwError "import mismatch: {a} (in {modOf a}) is under {sa}, {b} (in {modOf b}) is under {sb}"
  logInfo m!"same_imports {a} {b}: ok"

syntax (name := stmtHash) "#statement_hash " ident : command

@[command_elab stmtHash] def elabStmtHash : CommandElab := fun stx => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  logInfo m!"statement_hash {n} {← liftCoreM (statementHash n)}"

end Verify.Eval.H

namespace Verify.Eval.H
open Lean Elab Command

/-- `#expect_reject in cmd` elaborates `cmd` and passes only if it reports an error, which it
swallows; a command that passes fails the file. For negative tests of the checks above. -/
syntax (name := expectReject) "#expect_reject " "in" ppLine command : command

@[command_elab expectReject] def elabExpectReject : CommandElab := fun stx => do
  let saved ← modifyGet fun s => (s.messages, { s with messages := {} })
  elabCommand stx[2]
  let new := (← get).messages
  modify fun s => { s with messages := saved }
  match new.toList.find? (·.severity == .error) with
  | some m => logInfo m!"rejected as expected: {((← m.toString).take 200)}"
  | none => throwError "EXPECTED REJECTION, but the command passed"

end Verify.Eval.H
