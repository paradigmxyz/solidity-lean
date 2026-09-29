import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 6000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace StorageRefNarrowKey

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def itemTy : Ty := Ty.user { segments := ["Item"] }
private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"
private def narrowKey : Expr := Expr.binary BinaryOp.add a b
private def keyedItem : Expr := Expr.index (Expr.ident "items") narrowKey

private def params : List Parameter :=
  [ { name := some "a", ty := Ty.uint 8, location := none }
  , { name := some "b", ty := Ty.uint 8, location := none } ]

private def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.structDecl
          { name := "Item", fields := [{ name := "value", ty := Ty.uint 256 }] }
      , ContractItem.stateVar
          { name := "items"
            ty := Ty.mapping (Ty.uint 256) itemTy
            visibility := some Visibility.internal_
            mutability := VarMutability.mutable
            override? := none
            init := none }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "touch"
            visibility := some Visibility.internal_
            mutability := StateMutability.nonpayable
            params :=
              [{ name := some "item", ty := itemTy,
                 location := some DataLocation.storage }]
            returns := []
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [Stmt.expr (Expr.assign (Expr.member (Expr.ident "item") "value")
                AssignOp.assign (Expr.literal (Literal.number "9")))]) }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "localRef"
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            params := params
            returns := [{ name := none, ty := Ty.uint 256, location := none }]
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [ Stmt.varDecl
                  [{ name := some "item", ty := itemTy,
                     location := some DataLocation.storage }]
                  (some keyedItem)
              , Stmt.expr (Expr.assign (Expr.member (Expr.ident "item") "value")
                  AssignOp.assign (Expr.literal (Literal.number "7")))
              , Stmt.returnValues (some (Expr.member (Expr.ident "item") "value")) ]) }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "internalArg"
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            params := params
            returns := [{ name := none, ty := Ty.uint 256, location := none }]
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [ Stmt.expr (Expr.call (Expr.ident "touch") [Arg.positional keyedItem])
              , Stmt.returnValues (some (Expr.literal (Literal.number "9"))) ]) } ] }

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def local_ref_key_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 400 contract "localRef" State.empty
    [Value.word 200, Value.word 100] 17

private def internal_arg_key_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 400 contract "internalArg" State.empty
    [Value.word 200, Value.word 100] 17

#guard isOkTrue local_ref_key_overflow_panics
#guard isOkTrue internal_arg_key_overflow_panics

end StorageRefNarrowKey
end Witness
end Solidity
end SolidCore
