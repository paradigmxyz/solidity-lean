import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
An explicit enum conversion evaluates its integer argument before checking the
enum range. For `EN(a + b)` with uint8 values 200 and 100, checked addition must
therefore Panic(0x11); only a successfully computed integer outside 0..2 should
Panic(0x21). This witness uses the same unresolved `Ty.user` enum conversion
shape produced by the Solidity importer, so normal enum resolution remains in
the checked execution path.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace EnumConversionNarrowOverflow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (value : String) : Expr := Expr.literal (Literal.number value)
private def enumTy : Ty := Ty.user { segments := ["EN"] }
private def enumValue (value : Expr) : Expr :=
  Expr.call (Expr.typeName enumTy) [Arg.positional value]
private def asWord (value : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256))
    [Arg.positional (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional value])]

private def checkedFunction (name aValue bValue : String) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      body := some (Stmt.block
        [ Stmt.varDecl [{ name := some "a", ty := Ty.uint 8, location := none }]
            (some (num aValue))
        , Stmt.varDecl [{ name := some "b", ty := Ty.uint 8, location := none }]
            (some (num bValue))
        , Stmt.varDecl [{ name := some "e", ty := enumTy, location := none }]
            (some (enumValue (Expr.binary BinaryOp.add
              (Expr.ident "a") (Expr.ident "b"))))
        , Stmt.returnValues (some (asWord (Expr.ident "e"))) ]) }

private def rangeFunction : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some "rangeOnly"
      visibility := some Visibility.external_
      mutability := StateMutability.pure
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      body := some (Stmt.block
        [ Stmt.varDecl [{ name := some "x", ty := Ty.uint 256, location := none }]
            (some (num "3"))
        , Stmt.varDecl [{ name := some "e", ty := enumTy, location := none }]
            (some (enumValue (Expr.ident "x")))
        , Stmt.returnValues (some (asWord (Expr.ident "e"))) ]) }

def contract : ContractDecl :=
  { name := "EnumConversionNarrowOverflow"
    items :=
      [ ContractItem.enumDecl { name := "EN", cases := ["A", "B", "C"] }
      , checkedFunction "run" "200" "100"
      , checkedFunction "safe" "1" "1"
      , rangeFunction ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def overflowPanicsFirst : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "run" State.empty [] 0x11
def safeReturnsTwo : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 300 contract "safe" State.empty [] 2
def rangePanicsAfterEvaluation : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "rangeOnly" State.empty [] 0x21

#guard accepted
#guard isOkTrue overflowPanicsFirst
#guard isOkTrue safeReturnsTwo
#guard isOkTrue rangePanicsAfterEvaluation

end EnumConversionNarrowOverflow
end Witness
end Solidity
end SolidCore
