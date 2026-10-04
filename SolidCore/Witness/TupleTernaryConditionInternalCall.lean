import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-! A tuple-assignment component can contain a ternary whose condition contains
an internal call. The condition is evaluated before the selected pure branch. -/

namespace SolidCore.Solidity.Witness.TupleTernaryConditionInternalCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (n : String) : Expr := Expr.literal (Literal.number n)

private def idFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "id"
    visibility := some Visibility.internal_
    mutability := StateMutability.pure
    params := [{ name := some "x", ty := Ty.uint 256 }]
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) }

private def condition : Expr :=
  Expr.binary BinaryOp.ne
    (Expr.call (Expr.ident "id") [Arg.positional (Expr.ident "a")])
    (num "0")

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    params :=
      [{ name := some "a", ty := Ty.uint 8 },
       { name := some "b", ty := Ty.uint 8 }]
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "result", ty := Ty.uint 256 }] none
      , Stmt.expr (Expr.assign
          (Expr.tuple [TupleItem.value (Expr.ident "result"), TupleItem.hole])
          AssignOp.assign
          (Expr.tuple
            [ TupleItem.value
                (Expr.ternary condition (Expr.ident "a") (Expr.ident "b"))
            , TupleItem.value (Expr.ident "b") ]))
      , Stmt.returnValues (some (Expr.ident "result")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items := [ContractItem.function idFn, ContractItem.function runFn] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def trueBranchMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty
    [Value.word 1, Value.word 2] 1

def falseBranchMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty
    [Value.word 0, Value.word 2] 2

#guard accepted
#guard isOkTrue trueBranchMatches
#guard isOkTrue falseBranchMatches

end SolidCore.Solidity.Witness.TupleTernaryConditionInternalCall
