import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
The constructor's `this.run` value needs the same most-derived `this` type
binding as state initializers. The checked constructor stores the ABI hash of
the bound external function value, then `run` reads it back.
-/

namespace SolidCore.Solidity.Witness.ConstructorBoundExternalFunctionValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def constructorFn : FunctionDecl :=
  { kind := FunctionKind.constructor
    visibility := some Visibility.public_
    mutability := StateMutability.nonpayable
    body := some (Stmt.block
      [Stmt.expr (Expr.assign (Expr.ident "value") AssignOp.assign
        (Expr.call (Expr.ident "keccak256")
          [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode")
            [Arg.positional (Expr.member (Expr.ident "this") "run")])]))]) }

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.view
    returns := [{ name := none, ty := Ty.bytesN 32 }]
    body := some (Stmt.block
      [Stmt.returnValues (some (Expr.ident "value"))]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar { name := "value", ty := Ty.bytesN 32 }
      , ContractItem.function constructorFn
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

def constructsAndStores : Except TypeError Bool := do
  let state ← Examples.checkedConstructState 4096 sourceUnit "C" []
  Except.ok (!wordEq (state.loadSlot 0) 0)

#guard accepted
#guard isOkTrue constructsAndStores

end SolidCore.Solidity.Witness.ConstructorBoundExternalFunctionValue
