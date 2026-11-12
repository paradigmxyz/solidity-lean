-- Generated from scripts/refinement/events/events.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace Events

def importedSourceName : String := "scripts/refinement/events/events.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Events"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Transfer",
    params := [{ name := some "from", ty := Ty.address false, indexed := true }, { name := some "id", ty := Ty.uint 256, indexed := true }, { name := some "value", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "transfer",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "id", ty := Ty.uint 256, location := none }, { name := some "value", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "Transfer") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "id"), Arg.positional (Expr.ident "value")])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Events
end Source
end Refinement
end SolidCore
