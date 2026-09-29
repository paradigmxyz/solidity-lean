import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

namespace SolidCore
namespace Solidity
namespace Witness
namespace BuiltinStrayIdentifier

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.function
          { kind := FunctionKind.function
            name := some "f"
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            params := []
            returns := [{ name := none, ty := Ty.uint 256, location := none }]
            virtual := false
            override? := none
            modifiers := []
            body := some (Stmt.block
              [ Stmt.expr (Expr.ident "msg")
              , Stmt.expr (Expr.ident "keccak256")
              , Stmt.expr (Expr.ident "addmod")
              , Stmt.returnValues (some (Expr.literal (Literal.number "1"))) ]) } ] }

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

private def builtin_stray_values_are_noops : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 64 contract "f" State.empty [] 1

#guard isOkTrue builtin_stray_values_are_noops

end BuiltinStrayIdentifier
end Witness
end Solidity
end SolidCore
