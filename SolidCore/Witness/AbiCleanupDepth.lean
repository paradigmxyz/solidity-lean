import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 4000000

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiCleanupDepth

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def wrapBitOr : Nat -> Expr -> Expr
  | 0, expr => expr
  | depth + 1, expr =>
      wrapBitOr depth
        (Expr.binary BinaryOp.bitOr expr (Expr.literal (Literal.number "0")))

private def contract : ContractDecl :=
  let sum := Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")
  let nested := wrapBitOr 9 sum
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            visibility := some Visibility.external_
            mutability := StateMutability.pure
            params :=
              [ { name := some "a", ty := Ty.uint 8, location := none }
              , { name := some "b", ty := Ty.uint 8, location := none } ]
            returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }]
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [Stmt.returnValues
                (some (Expr.call (Expr.member (Expr.ident "abi") "encode")
                  [Arg.positional nested]))]) } ] }

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def depth_nine_overflow_panics : Except TypeError Bool :=
  Examples.checkedOwnCallPanicMatches 400 contract "f" State.empty
    [Value.word 200, Value.word 100] 17

#guard isOkTrue depth_nine_overflow_panics

end AbiCleanupDepth
end Witness
end Solidity
end SolidCore
