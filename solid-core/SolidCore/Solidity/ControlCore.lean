import SolidCore.Solidity.Interpreter

namespace SolidCore
namespace Solidity
namespace ControlCore

abbrev Word := Source.Word
abbrev Ty := Source.Ty
abbrev Value := Source.Value
abbrev Expr := Source.Expr
abbrev LValue := Source.LValue
abbrev Context := Source.Context
abbrev Runtime := Source.Runtime
abbrev Result := Source.Result
abbrev RevertData := Source.RevertData

inductive Stmt where
  | skip : Stmt
  | block : List Stmt -> Stmt
  | varDecl : Ty -> String -> Option Expr -> Stmt
  | assign : LValue -> Expr -> Stmt
  | assignOp : LValue -> Source.BinaryOp -> Expr -> Stmt
  | ifElse : Expr -> Stmt -> Stmt -> Stmt
  | switch : Expr -> List (Word × Stmt) -> Option Stmt -> Stmt
  | whileLoop : Expr -> Stmt -> Stmt
  | forLoop : Stmt -> Expr -> Stmt -> Stmt -> Stmt
  | break : Stmt
  | continue : Stmt
  | returnValues : List Expr -> Stmt
  | revert : String -> List Expr -> Stmt
  | emitEvent : String -> List Expr -> Stmt
  | unchecked : Stmt -> Stmt
  deriving Repr

mutual

def Stmt.ofSource : Source.Stmt -> Stmt
  | Source.Stmt.skip => Stmt.skip
  | Source.Stmt.block body => Stmt.block (Stmt.listOfSource body)
  | Source.Stmt.varDecl ty name init => Stmt.varDecl ty name init
  | Source.Stmt.assign target expr => Stmt.assign target expr
  | Source.Stmt.assignOp target op expr => Stmt.assignOp target op expr
  | Source.Stmt.ifElse cond thenBranch elseBranch =>
      Stmt.ifElse cond (Stmt.ofSource thenBranch) (Stmt.ofSource elseBranch)
  | Source.Stmt.switch discr cases defaultBranch =>
      Stmt.switch discr (Stmt.switchCasesOfSource cases)
        (Stmt.optionalOfSource defaultBranch)
  | Source.Stmt.whileLoop cond body => Stmt.whileLoop cond (Stmt.ofSource body)
  | Source.Stmt.forLoop init cond post body =>
      Stmt.forLoop (Stmt.ofSource init) cond (Stmt.ofSource post)
        (Stmt.ofSource body)
  | Source.Stmt.break => Stmt.break
  | Source.Stmt.continue => Stmt.continue
  | Source.Stmt.returnValues exprs => Stmt.returnValues exprs
  | Source.Stmt.revert name exprs => Stmt.revert name exprs
  | Source.Stmt.emitEvent name exprs => Stmt.emitEvent name exprs
  | Source.Stmt.unchecked body => Stmt.unchecked (Stmt.ofSource body)

def Stmt.listOfSource : List Source.Stmt -> List Stmt
  | [] => []
  | stmt :: rest => Stmt.ofSource stmt :: Stmt.listOfSource rest

def Stmt.switchCasesOfSource :
    List (Word × Source.Stmt) -> List (Word × Stmt)
  | [] => []
  | (label, branch) :: rest =>
      (label, Stmt.ofSource branch) :: Stmt.switchCasesOfSource rest

def Stmt.optionalOfSource : Option Source.Stmt -> Option Stmt
  | none => none
  | some stmt => some (Stmt.ofSource stmt)

end

mutual

def Stmt.toSource : Stmt -> Source.Stmt
  | Stmt.skip => Source.Stmt.skip
  | Stmt.block body => Source.Stmt.block (Stmt.listToSource body)
  | Stmt.varDecl ty name init => Source.Stmt.varDecl ty name init
  | Stmt.assign target expr => Source.Stmt.assign target expr
  | Stmt.assignOp target op expr => Source.Stmt.assignOp target op expr
  | Stmt.ifElse cond thenBranch elseBranch =>
      Source.Stmt.ifElse cond (Stmt.toSource thenBranch)
        (Stmt.toSource elseBranch)
  | Stmt.switch discr cases defaultBranch =>
      Source.Stmt.switch discr (Stmt.switchCasesToSource cases)
        (Stmt.optionalToSource defaultBranch)
  | Stmt.whileLoop cond body => Source.Stmt.whileLoop cond (Stmt.toSource body)
  | Stmt.forLoop init cond post body =>
      Source.Stmt.forLoop (Stmt.toSource init) cond (Stmt.toSource post)
        (Stmt.toSource body)
  | Stmt.break => Source.Stmt.break
  | Stmt.continue => Source.Stmt.continue
  | Stmt.returnValues exprs => Source.Stmt.returnValues exprs
  | Stmt.revert name exprs => Source.Stmt.revert name exprs
  | Stmt.emitEvent name exprs => Source.Stmt.emitEvent name exprs
  | Stmt.unchecked body => Source.Stmt.unchecked (Stmt.toSource body)

def Stmt.listToSource : List Stmt -> List Source.Stmt
  | [] => []
  | stmt :: rest => Stmt.toSource stmt :: Stmt.listToSource rest

def Stmt.switchCasesToSource :
    List (Word × Stmt) -> List (Word × Source.Stmt)
  | [] => []
  | (label, branch) :: rest =>
      (label, Stmt.toSource branch) :: Stmt.switchCasesToSource rest

def Stmt.optionalToSource : Option Stmt -> Option Source.Stmt
  | none => none
  | some stmt => some (Stmt.toSource stmt)

end

def Stmt.findSwitchBranch? (value : Word) : List (Word × Stmt) -> Option Stmt
  | [] => none
  | (label, body) :: rest =>
      if Source.wordEq label value then
        some body
      else
        Stmt.findSwitchBranch? value rest

mutual

/-- Independent executable candidate for ControlCore statements.
It is not used by the public `compile?` soundness theorem until its bridge to
`toSource` is proved and maintained compositionally. -/
def Stmt.evalCore (fuel : Nat) (context : Context)
    (runtime : Runtime) : Stmt -> Option Result :=
  match fuel with
  | 0 => fun _ => none
  | fuel + 1 => fun stmt =>
      match stmt with
      | Stmt.skip => some (Source.Result.normal runtime)
      | Stmt.block body =>
          match Stmt.evalListCore fuel context runtime.pushScope body with
          | some result => some (result.mapRuntime Source.Runtime.popScope)
          | none => none
      | Stmt.varDecl ty name init =>
          match init with
          | some expr =>
              match expr.eval context runtime with
              | Except.ok value =>
                  some (Source.Result.normal (runtime.declareLocal name value))
              | Except.error err =>
                  some (Source.Result.reverted runtime err)
          | none =>
              some
                (Source.Result.normal
                  (runtime.declareLocal name ty.defaultValue))
      | Stmt.assign target expr =>
          match expr.eval context runtime with
          | Except.ok value =>
              match target.write context runtime value with
              | Except.ok updated => some (Source.Result.normal updated)
              | Except.error err => some (Source.Result.reverted runtime err)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.assignOp target op expr =>
          match target.read context runtime, expr.eval context runtime with
          | Except.ok lhs, Except.ok rhs =>
              match Source.BinaryOp.apply context.checked op lhs rhs with
              | Except.ok value =>
                  match target.write context runtime value with
                  | Except.ok updated => some (Source.Result.normal updated)
                  | Except.error err => some (Source.Result.reverted runtime err)
              | Except.error err => some (Source.Result.reverted runtime err)
          | Except.error err, _ => some (Source.Result.reverted runtime err)
          | _, Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.ifElse cond thenBranch elseBranch =>
          match cond.eval context runtime with
          | Except.ok value =>
              match value.expectWord with
              | Except.ok word =>
                  if Source.wordTruthy word then
                    Stmt.evalCore fuel context runtime thenBranch
                  else
                    Stmt.evalCore fuel context runtime elseBranch
              | Except.error err => some (Source.Result.reverted runtime err)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.switch discr cases defaultBranch =>
          match discr.eval context runtime with
          | Except.ok value =>
              match value.expectWord with
              | Except.ok word =>
                  match Stmt.findSwitchBranch? word cases, defaultBranch with
                  | some branch, _ => Stmt.evalCore fuel context runtime branch
                  | none, some branch => Stmt.evalCore fuel context runtime branch
                  | none, none => some (Source.Result.normal runtime)
              | Except.error err => some (Source.Result.reverted runtime err)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.whileLoop cond body =>
          Stmt.evalWhileCore fuel context runtime cond body
      | Stmt.forLoop init cond post body =>
          let loopRuntime := runtime.pushScope
          match Stmt.evalCore fuel context loopRuntime init with
          | some (Source.Result.normal initialized) =>
              match Stmt.evalForCore fuel context initialized cond post body with
              | some result => some (result.mapRuntime Source.Runtime.popScope)
              | none => none
          | some result => some (result.mapRuntime Source.Runtime.popScope)
          | none => none
      | Stmt.break => some (Source.Result.broke runtime)
      | Stmt.continue => some (Source.Result.continued runtime)
      | Stmt.returnValues exprs =>
          match Source.Expr.evalList context runtime exprs with
          | Except.ok values => some (Source.Result.returned runtime values)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.revert name exprs =>
          match Source.Expr.evalList context runtime exprs with
          | Except.ok values =>
              some
                (Source.Result.reverted runtime
                  (Source.RevertData.custom name values))
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.emitEvent name exprs =>
          match Source.Expr.evalList context runtime exprs with
          | Except.ok values =>
              match runtime.emitEvent context name values with
              | Except.ok updated => some (Source.Result.normal updated)
              | Except.error err => some (Source.Result.reverted runtime err)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Stmt.unchecked body =>
          Stmt.evalCore fuel { context with checked := false } runtime body

def Stmt.evalListCore (fuel : Nat) (context : Context)
    (runtime : Runtime) : List Stmt -> Option Result
  | [] => some (Source.Result.normal runtime)
  | stmt :: rest =>
      match Stmt.evalCore fuel context runtime stmt with
      | some (Source.Result.normal runtime') =>
          Stmt.evalListCore fuel context runtime' rest
      | some result => some result
      | none => none

def Stmt.evalWhileCore (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.eval context runtime with
      | Except.ok value =>
          match value.expectWord with
          | Except.ok word =>
              if Source.wordTruthy word then
                match Stmt.evalCore fuel context runtime body with
                | some (Source.Result.normal runtime') =>
                    Stmt.evalWhileCore fuel context runtime' cond body
                | some (Source.Result.continued runtime') =>
                    Stmt.evalWhileCore fuel context runtime' cond body
                | some (Source.Result.broke runtime') =>
                    some (Source.Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Source.Result.normal runtime)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Except.error err => some (Source.Result.reverted runtime err)

def Stmt.evalForCore (fuel : Nat) (context : Context)
    (runtime : Runtime) (cond : Expr) (post : Stmt) (body : Stmt) :
    Option Result :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match cond.eval context runtime with
      | Except.ok value =>
          match value.expectWord with
          | Except.ok word =>
              if Source.wordTruthy word then
                match Stmt.evalCore fuel context runtime body with
                | some (Source.Result.normal runtime') =>
                    match Stmt.evalCore fuel context runtime' post with
                    | some (Source.Result.normal posted) =>
                        Stmt.evalForCore fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Source.Result.continued runtime') =>
                    match Stmt.evalCore fuel context runtime' post with
                    | some (Source.Result.normal posted) =>
                        Stmt.evalForCore fuel context posted cond post body
                    | some result => some result
                    | none => none
                | some (Source.Result.broke runtime') =>
                    some (Source.Result.normal runtime')
                | some result => some result
                | none => none
              else
                some (Source.Result.normal runtime)
          | Except.error err => some (Source.Result.reverted runtime err)
      | Except.error err => some (Source.Result.reverted runtime err)

end

/-- Projection semantics used by the current source-to-ControlCore theorem. -/
def Stmt.eval (fuel : Nat) (context : Context)
    (runtime : Runtime) (stmt : Stmt) : Option Result :=
  Source.Stmt.eval fuel context runtime stmt.toSource

def Stmt.compile (stmt : Source.Stmt) : Stmt :=
  Stmt.ofSource stmt

def Stmt.compile? (stmt : Source.Stmt) : Option Stmt :=
  some (Stmt.compile stmt)

mutual

theorem Stmt.toSource_ofSource (stmt : Source.Stmt) :
    (Stmt.ofSource stmt).toSource = stmt := by
  cases stmt with
  | skip => rfl
  | block body =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.listToSource_of_listOfSource]
  | varDecl ty name init => rfl
  | assign target expr => rfl
  | assignOp target op expr => rfl
  | ifElse cond thenBranch elseBranch =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.toSource_ofSource thenBranch,
        Stmt.toSource_ofSource elseBranch]
  | switch discr cases defaultBranch =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.switchCasesToSource_of_switchCasesOfSource,
        Stmt.optionalToSource_of_optionalOfSource]
  | whileLoop cond body =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.toSource_ofSource body]
  | forLoop init cond post body =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.toSource_ofSource init,
        Stmt.toSource_ofSource post,
        Stmt.toSource_ofSource body]
  | «break» => rfl
  | «continue» => rfl
  | returnValues exprs => rfl
  | revert name exprs => rfl
  | emitEvent name exprs => rfl
  | unchecked body =>
      simp [Stmt.ofSource, Stmt.toSource,
        Stmt.toSource_ofSource body]

theorem Stmt.listToSource_of_listOfSource (stmts : List Source.Stmt) :
    Stmt.listToSource (Stmt.listOfSource stmts) = stmts := by
  cases stmts <;>
    simp [Stmt.listOfSource, Stmt.listToSource, Stmt.toSource_ofSource,
      Stmt.listToSource_of_listOfSource]

theorem Stmt.switchCasesToSource_of_switchCasesOfSource
    (cases : List (Word × Source.Stmt)) :
    Stmt.switchCasesToSource (Stmt.switchCasesOfSource cases) = cases := by
  cases cases with
  | nil =>
      simp [Stmt.switchCasesOfSource, Stmt.switchCasesToSource]
  | cons head rest =>
      rcases head with ⟨label, branch⟩
      simp [Stmt.switchCasesOfSource, Stmt.switchCasesToSource,
        Stmt.toSource_ofSource,
        Stmt.switchCasesToSource_of_switchCasesOfSource]

theorem Stmt.optionalToSource_of_optionalOfSource
    (stmt : Option Source.Stmt) :
    Stmt.optionalToSource (Stmt.optionalOfSource stmt) = stmt := by
  cases stmt <;>
    simp [Stmt.optionalOfSource, Stmt.optionalToSource,
      Stmt.toSource_ofSource]

end

theorem Stmt.eval_ofSource (fuel : Nat) (context : Context)
    (runtime : Runtime) (stmt : Source.Stmt) :
  Stmt.eval fuel context runtime (Stmt.ofSource stmt) =
      Source.Stmt.eval fuel context runtime stmt := by
  simp [Stmt.eval, Stmt.toSource_ofSource]

theorem Stmt.compile?_complete (stmt : Source.Stmt) :
    Stmt.compile? stmt = some (Stmt.compile stmt) := by
  rfl

theorem Stmt.compile?_sound
    {stmt : Source.Stmt} {core : Stmt}
    (hCompile : Stmt.compile? stmt = some core)
    (fuel : Nat) (context : Context) (runtime : Runtime) :
    Stmt.eval fuel context runtime core =
      Source.Stmt.eval fuel context runtime stmt := by
  simp [Stmt.compile?, Stmt.compile] at hCompile
  cases hCompile
  exact Stmt.eval_ofSource fuel context runtime stmt

end ControlCore
end Solidity
end SolidCore
