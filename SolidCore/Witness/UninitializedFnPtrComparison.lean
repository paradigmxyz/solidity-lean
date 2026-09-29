/-
An uninitialised internal function pointer is the value zero. Comparing a
valid pointer with it succeeds and is false; only calling the zero pointer
panics 0x51.

This is the exact Spec Hunt shape: `internal1 == invalid` is assigned to a
named boolean return and the function falls through.
-/
import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace UninitializedFnPtrComparison

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [] [] [Ty.bool] [none]
    StateMutability.pure Visibility.internal_

private def internal1 : ContractItem := ContractItem.function
  { kind := FunctionKind.function
    name := some "internal1"
    visibility := some Visibility.internal_
    mutability := StateMutability.pure
    params := []
    returns := [{ name := none, ty := Ty.bool, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block []) }

private def equal : ContractItem := ContractItem.function
  { kind := FunctionKind.function
    name := some "equal"
    visibility := some Visibility.public_
    mutability := StateMutability.pure
    params := []
    returns :=
      [ { name := some "same", ty := Ty.bool, location := none }
      , { name := some "diff", ty := Ty.bool, location := none }
      , { name := some "inv", ty := Ty.bool, location := none } ]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "invalid", ty := fnPtrTy, location := none }] none
      , Stmt.expr
          (Expr.assign (Expr.ident "inv") AssignOp.assign
            (Expr.binary BinaryOp.eq
              (Expr.ident "internal1") (Expr.ident "invalid"))) ]) }

def sourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract
          { kind := ContractKind.contract
            name := "C"
            abstract := false
            bases := []
            items := [internal1, equal] } ] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

def equalReturnsFalseTriple : Except TypeError Bool :=
  Examples.checkedCallValuesMatch 256 sourceUnit "C" "equal" State.empty []
    [Value.word 0, Value.word 0, Value.word 0]

#eval accepted
#eval equalReturnsFalseTriple

theorem accepted_eq_true : accepted = true := by native_decide

def equalReturnsFalseTripleOk : Bool :=
  match equalReturnsFalseTriple with
  | Except.ok true => true
  | _ => false

theorem equalReturnsFalseTripleOk_eq_true :
    equalReturnsFalseTripleOk = true := by native_decide

end UninitializedFnPtrComparison
end Witness
end Solidity
end SolidCore
