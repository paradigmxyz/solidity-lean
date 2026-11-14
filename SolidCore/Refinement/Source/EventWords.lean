-- Generated from scripts/refinement/mem/event_words.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace EventWords

def importedSourceName : String := "scripts/refinement/mem/event_words.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "EventWords"
  abstract := false
  bases := []
  items := [(ContractItem.eventDecl
  { name := "Swap",
    params := [{ name := some "sender", ty := Ty.address false, indexed := true }, { name := some "amount0In", ty := Ty.uint 256, indexed := false }, { name := some "amount1In", ty := Ty.uint 256, indexed := false }, { name := some "amount0Out", ty := Ty.uint 256, indexed := false }, { name := some "amount1Out", ty := Ty.uint 256, indexed := false }, { name := some "to", ty := Ty.address false, indexed := true }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "swap",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a0", ty := Ty.uint 256, location := none }, { name := some "a1", ty := Ty.uint 256, location := none }, { name := some "b0", ty := Ty.uint 256, location := none }, { name := some "b1", ty := Ty.uint 256, location := none }, { name := some "to", ty := Ty.address false, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.emitEvent (Expr.call (Expr.ident "Swap") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "a0"), Arg.positional (Expr.ident "a1"), Arg.positional (Expr.ident "b0"), Arg.positional (Expr.ident "b1"), Arg.positional (Expr.ident "to")])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EventWords
end Source
end Refinement
end SolidCore
