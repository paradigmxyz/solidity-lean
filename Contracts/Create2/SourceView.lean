-- Generated from Contracts/Create2/Deployer.sol with solc 0.8.35 by scripts/verify/create2_sources.py. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Verify
namespace Create2
namespace SourceView

def importedSourceName : String := "Contracts/Create2/Deployer.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Deployer"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "deploy",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "salt", ty := Ty.bytesN 32, location := none }],
    returns := [{ name := some "a", ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "code", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.literal (Literal.hexString "6001600c60003960016000f300"))), Stmt.assemblyCreate2 (Expr.ident "a") (Expr.literal (Literal.number "0")) (Expr.ident "code") (Expr.ident "salt")]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "deployWith",
    visibility := some Visibility.external_,
    mutability := StateMutability.payable,
    params := [{ name := some "v", ty := Ty.uint 256, location := none }, { name := some "salt", ty := Ty.uint 256, location := none }, { name := some "code", ty := Ty.bytes, location := some DataLocation.memory }],
    returns := [{ name := some "a", ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.assemblyCreate2 (Expr.ident "a") (Expr.ident "v") (Expr.ident "code") (Expr.ident "salt")]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SourceView
end Create2
end Verify
end SolidCore
