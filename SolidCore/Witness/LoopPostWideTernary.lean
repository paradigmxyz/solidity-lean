import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-! A mixed-width ternary nested under a bitwise operation in a loop post
expression takes the common uint256 type. The unselected uint8 branch must not
narrow the selected uint256 addition. -/

namespace SolidCore.Solidity.Witness.LoopPostWideTernary

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (n : String) : Expr := Expr.literal (Literal.number n)

private def postRhs : Expr :=
  Expr.binary BinaryOp.bitOr
    (Expr.ternary (Expr.ident "flag")
      (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (num "1")])
      (Expr.binary BinaryOp.add (Expr.ident "first") (Expr.ident "second")))
    (num "1")

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    params := [{ name := some "flag", ty := Ty.bool }]
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [ Stmt.varDecl [{ name := some "first", ty := Ty.uint 256 }] (some (num "128"))
      , Stmt.varDecl [{ name := some "second", ty := Ty.uint 256 }] (some (num "128"))
      , Stmt.varDecl [{ name := some "result", ty := Ty.uint 256 }] none
      , Stmt.forLoop
          (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256 }] none))
          (some (Expr.binary BinaryOp.lt (Expr.ident "i") (num "1")))
          (some (Expr.assign (Expr.ident "i") AssignOp.addAssign postRhs))
          (Stmt.block
            [Stmt.expr (Expr.assign (Expr.ident "result") AssignOp.addAssign
              (Expr.binary BinaryOp.add (Expr.ident "i") (num "1")))])
      , Stmt.returnValues (some (Expr.ident "result")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items := [ContractItem.function runFn] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def wideBranchMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty
    [Value.word 0] 1

def narrowBranchMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty
    [Value.word 1] 1

#guard accepted
#guard isOkTrue wideBranchMatches
#guard isOkTrue narrowBranchMatches

end SolidCore.Solidity.Witness.LoopPostWideTernary
