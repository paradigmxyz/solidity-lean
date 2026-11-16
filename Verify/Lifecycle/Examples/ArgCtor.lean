-- The solc-AST front end's output for tools/certify/examples/lifecycle/ArgCtor.sol (solar 0479b90a), as
-- tools/certify/generic.py writes it, under Verify.Lifecycle.Examples.ArgCtor.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace Verify
namespace Lifecycle
namespace Examples
namespace ArgCtor

def importedSourceName : String := "ArgCtor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ArgCtor"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "x",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "owner",
    ty := Ty.address false,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x0", ty := Ty.uint 256, location := none }, { name := some "owner0", ty := Ty.address false, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "x") AssignOp.assign (Expr.ident "x0")), Stmt.expr (Expr.assign (Expr.ident "owner") AssignOp.assign (Expr.ident "owner0"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ArgCtor
end Examples
end Lifecycle
end Verify
