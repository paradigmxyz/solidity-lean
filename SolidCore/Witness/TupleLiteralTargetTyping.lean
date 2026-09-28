import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Tuple declarations and assignments carry a target type for each component.
Bare string and hex literals bound to bytesN components must use that target,
matching the already-correct single declaration form, rather than remaining a
dynamic byte-string value that panics during tuple assignment.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleLiteralTargetTyping

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (value : String) : Expr := Expr.literal (Literal.number value)
private def u256 (value : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional value]
private def valueAsWord : Expr :=
  u256 (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.ident "value")])
private def result : Expr :=
  Expr.binary BinaryOp.add valueAsWord (Expr.ident "other")
private def valueBinding : VarBinding :=
  { name := some "value", ty := Ty.bytesN 4, location := none }
private def otherBinding : VarBinding :=
  { name := some "other", ty := Ty.uint 256, location := none }
private def bindings : List VarBinding := [valueBinding, otherBinding]
private def tupleRhs (literal : Literal) (other : String) : Expr :=
  Expr.tuple
    [ TupleItem.value (Expr.literal literal)
    , TupleItem.value (u256 (num other)) ]

private def declarationFunction
    (name : Name) (literal : Literal) (other : String) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      body := some (Stmt.block
        [ Stmt.varDecl bindings (some (tupleRhs literal other))
        , Stmt.returnValues (some result) ]) }

private def assignmentFunction : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "hexAssignment"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      body := some (Stmt.block
        [ Stmt.varDecl [valueBinding] none
        , Stmt.varDecl [otherBinding] none
        , Stmt.expr (Expr.assign
            (Expr.tuple
              [TupleItem.value (Expr.ident "value"), TupleItem.value (Expr.ident "other")])
            AssignOp.assign
            (tupleRhs (Literal.hexString "11223344") "3"))
        , Stmt.returnValues (some result) ]) }

def contract : ContractDecl :=
  { name := "TupleLiteralTargetTyping"
    items :=
      [ declarationFunction "hexDeclaration" (Literal.hexString "11223344") "1"
      , declarationFunction "stringDeclaration" (Literal.string "abcd") "2"
      , assignmentFunction ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def hexDeclarationMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "hexDeclaration" State.empty [] 287454021
def stringDeclarationMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "stringDeclaration" State.empty [] 1633837926
def hexAssignmentMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "hexAssignment" State.empty [] 287454023

#guard accepted
#guard isOkTrue hexDeclarationMatches
#guard isOkTrue stringDeclarationMatches
#guard isOkTrue hexAssignmentMatches

end TupleLiteralTargetTyping
end Witness
end Solidity
end SolidCore
