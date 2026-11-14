-- Generated from scripts/refinement/mem/try_catch.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace TryCatch

def importedSourceName : String := "scripts/refinement/mem/try_catch.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.interface
  name := "IPrice"
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
  name := "TryCatch"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "priceOr",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "o", ty := Ty.user ({ segments := ["IPrice"] }), location := none }, { name := some "dflt", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.tryCatchReturns (Expr.call (Expr.member (Expr.ident "o") "price") []) [{ name := some "p", ty := Ty.uint 256, location := none }] (Stmt.block [Stmt.returnValues (some (Expr.ident "p"))]) [CatchClause.clause none [] (Stmt.block [Stmt.returnValues (some (Expr.ident "dflt"))])]]) })] }

def importedContract : ContractDecl :=
  importedContractDecl1

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TryCatch
end Source
end Refinement
end SolidCore
