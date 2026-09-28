import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Regression for fixed-bytes compound left shift. A bytesN compound assignment
must clean the result back to the LValue width before storing it. For bytes4,
0x11223344 shifted left by 8 yields 0x22334400, not 0x1122334400.
-/

namespace SolidCore.Solidity.Witness.BytesNCompoundShiftCleanup

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def b4 : Ty := Ty.bytesN 4
private def id (name : String) : Expr := Expr.ident name
private def num (value : String) : Expr := Expr.literal (Literal.number value)

private def probe (name : String) (op : AssignOp) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      params := []
      returns := [{ name := none, ty := b4, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some (Stmt.block
        [ Stmt.varDecl [{ name := some "b", ty := some b4 }]
            (some (num "0x11223344"))
        , Stmt.expr (Expr.assign (id "b") op (num "8"))
        , Stmt.returnValues (some (id "b")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ probe "left" AssignOp.shlAssign
      , probe "right" AssignOp.shrAssign ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract contract] }

private def ok : Except TypeCheck.TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

def left_is_masked : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "left" State.empty []
    0x22334400

def right_is_unchanged_semantics : Except TypeCheck.TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 contract "right" State.empty []
    0x00112233

#guard accepted
#guard ok left_is_masked
#guard ok right_is_unchanged_semantics

end SolidCore.Solidity.Witness.BytesNCompoundShiftCleanup
