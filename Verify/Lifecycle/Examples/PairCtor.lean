-- The solc-AST front end's output for tools/certify/examples/lifecycle/PairCtor.sol (solar 0479b90a), as
-- tools/certify/generic.py writes it, under Verify.Lifecycle.Examples.PairCtor.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace Verify
namespace Lifecycle
namespace Examples
namespace PairCtor

def importedSourceName : String := "PairCtor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "PairCtor"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "a",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "b",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a0", ty := Ty.uint 256, location := none }, { name := some "b0", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "a") AssignOp.assign (Expr.ident "a0")), Stmt.expr (Expr.assign (Expr.ident "b") AssignOp.assign (Expr.binary BinaryOp.add (Expr.ident "a0") (Expr.ident "b0")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "b"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end PairCtor
end Examples
end Lifecycle
end Verify
