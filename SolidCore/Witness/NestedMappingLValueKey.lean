import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 4000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace NestedMappingLValueKey

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def a : Expr := Expr.ident "a"
private def b : Expr := Expr.ident "b"
private def narrowAdd : Expr := Expr.binary BinaryOp.add a b
private def nestedAt (outer inner : Expr) : Expr :=
  Expr.index (Expr.index (Expr.ident "m") outer) inner

private def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.stateVar
          { name := "m"
            ty := Ty.mapping (Ty.uint 256)
              (Ty.mapping (Ty.uint 256) (Ty.uint 256))
            visibility := some Visibility.internal_
            mutability := VarMutability.mutable
            override? := none
            init := none }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            params :=
              [ { name := some "a", ty := Ty.uint 8, location := none }
              , { name := some "b", ty := Ty.uint 8, location := none } ]
            returns := [{ name := none, ty := Ty.uint 256, location := none }]
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [ Stmt.expr
                  (Expr.assign
                    (nestedAt narrowAdd (Expr.literal (Literal.number "0")))
                    AssignOp.assign (Expr.literal (Literal.number "1")))
              , Stmt.returnValues
                  (some (nestedAt (Expr.literal (Literal.number "44"))
                    (Expr.literal (Literal.number "0")))) ]) } ] }

private def accepted : Bool :=
  match ContractDecl.checkedContract contract with
  | Except.ok _ => true
  | Except.error _ => false

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 300 contract "f" State.empty
    [Value.word 200, Value.word 100] 17

#guard accepted
#guard isOkTrue overflow_panics

end NestedMappingLValueKey
end Witness
end Solidity
end SolidCore
