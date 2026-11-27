-- Generated from Certified/reader/reader.sol with solc 0.8.35 by scripts/solc_ast_to_lean_source.py. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Verify
namespace VC
namespace Source
namespace Reader

def importedSourceName : String := "Certified/reader/reader.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.interface
  name := "IOracle"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "price",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := none })] }

def importedContractDecl1 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Reader"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "read",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "o", ty := Ty.user ({ segments := ["IOracle"] }), location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.call (Expr.member (Expr.ident "o") "price") []) (Expr.literal (Literal.number "1"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Reader
end Source
end VC
end Verify
end SolidCore
