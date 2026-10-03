import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A returned storage reference to a nested array element must preserve its path
when the index uses checked uint256 arithmetic. The old path lowerer accepted
only narrow integer types, so `which % 2` fell back to a value assignment and
panicked instead of binding the returned pointer.
-/

namespace SolidCore.Solidity.Witness.ReturnedStorageRefWideIndex

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (n : String) : Expr := Expr.literal (Literal.number n)
private def arrayTy : Ty := Ty.array (Ty.uint 256) none
private def boxesAt (which : Expr) : Expr :=
  Expr.index (Expr.ident "boxes") which

private def selectFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "selectWords"
    visibility := some Visibility.internal_
    mutability := StateMutability.view
    params := [{ name := some "which", ty := Ty.uint 256 }]
    returns := [{ name := some "r", ty := arrayTy,
                  location := some DataLocation.storage }]
    body := some (Stmt.block
      [ Stmt.returnValues (some
          (boxesAt (Expr.binary BinaryOp.mod (Expr.ident "which") (num "2")))) ]) }

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "r", ty := some arrayTy,
             location := some DataLocation.storage }]
          (some (Expr.call (Expr.ident "selectWords")
            [Arg.positional (num "0")]))
      , Stmt.expr (Expr.call (Expr.member (Expr.ident "r") "push")
          [Arg.positional (num "18")])
      , Stmt.returnValues (some (Expr.member (boxesAt (num "0")) "length")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar
          { name := "boxes", ty := Ty.array arrayTy (some 2) }
      , ContractItem.function selectFn
      , ContractItem.function runFn ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returnsOne : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty [] 1

#guard accepted
#guard isOkTrue returnsOne

end SolidCore.Solidity.Witness.ReturnedStorageRefWideIndex
