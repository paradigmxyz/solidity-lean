import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
`abi.encode(value, this.target)` has a bound external function value even
though no target function type is written at the argument site. Its unique
checked signature supplies the ABI type and selector.
-/

namespace SolidCore.Solidity.Witness.AbiEncodeBoundExternalFunction

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def targetFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "target"
    visibility := some Visibility.external_
    mutability := StateMutability.pure
    params := [{ name := some "input", ty := Ty.uint 256 }]
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [Stmt.returnValues (some (Expr.ident "input"))]) }

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.bytesN 32 }]
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign (Expr.ident "value") AssignOp.assign
          (Expr.call (Expr.ident "keccak256")
            [Arg.positional
              (Expr.call (Expr.member (Expr.ident "abi") "encode")
                [ Arg.positional (Expr.ident "value")
                , Arg.positional
                    (Expr.member (Expr.ident "this") "target") ])]))
      , Stmt.returnValues (some (Expr.ident "value")) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar { name := "value", ty := Ty.bytesN 32 }
      , ContractItem.function targetFn
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

def executesAndStores : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "run" State.empty []
  Except.ok (!wordEq (state.loadSlot 0) 0)

#guard accepted
#guard isOkTrue executesAndStores

end SolidCore.Solidity.Witness.AbiEncodeBoundExternalFunction
