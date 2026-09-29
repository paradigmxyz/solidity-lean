import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace InternalLibraryFnPtrValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [] [] [Ty.uint 256] [none]
    StateMutability.nonpayable Visibility.internal_

private def libraryFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function
    name := some "f"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    params := []
    returns := [{ name := none, ty := Ty.uint 256, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block []) }

def libraryDecl : ContractDecl :=
  { kind := ContractKind.library
    name := "L"
    abstract := false
    bases := []
    items := [libraryFn] }

private def gFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function
    name := some "g"
    visibility := some Visibility.public_
    mutability := StateMutability.nonpayable
    params := []
    returns := [{ name := none, ty := Ty.uint 256, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "ptr", ty := fnPtrTy, location := none }] none
      , Stmt.expr
          (Expr.assign (Expr.ident "ptr") AssignOp.assign
            (Expr.member
              (Expr.typeName (Ty.user { segments := ["L"] })) "f")) ]) }

def contractDecl : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items := [gFn] }

def sourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract libraryDecl
      , SourceItem.contract contractDecl ] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

def gReturnsZero : Except TypeError Bool :=
  Examples.checkedCallWordMatches 256 sourceUnit "C" "g" State.empty [] 0

#eval accepted
#eval gReturnsZero

theorem accepted_eq_true : accepted = true := by native_decide

def gReturnsZeroOk : Bool :=
  match gReturnsZero with
  | Except.ok true => true
  | _ => false

theorem gReturnsZeroOk_eq_true : gReturnsZeroOk = true := by native_decide

end InternalLibraryFnPtrValue
end Witness
end Solidity
end SolidCore
