-- Generated from scripts/refinement/mem/event_dyn.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace EventDyn

def importedSourceName : String := "scripts/refinement/mem/event_dyn.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "EventDyn"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Note",
    params := [{ name := some "who", ty := Ty.address false, indexed := true }, { name := some "data", ty := Ty.bytes, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "note",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "data", ty := Ty.bytes, location := some DataLocation.calldata }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "Note") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "data")])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EventDyn
end Source
end Refinement
end SolidCore
