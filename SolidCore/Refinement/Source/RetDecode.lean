-- Generated from scripts/refinement/mem/ret_decode.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace RetDecode

def importedSourceName : String := "scripts/refinement/mem/ret_decode.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.interface
  name := "IToken"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "balanceOf",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "owner", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := none })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "RetDecode"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "held",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "token", ty := Ty.user ({ segments := ["IToken"] }), location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "token") "balanceOf") [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.ident "this")])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RetDecode
end Source
end Refinement
end SolidCore
