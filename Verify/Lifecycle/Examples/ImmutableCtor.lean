-- The solc-AST front end's output for tools/certify/examples/lifecycle/ImmutableCtor.sol (solar 0479b90a), as
-- tools/certify/generic.py writes it, under Verify.Lifecycle.Examples.ImmutableCtor.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace Verify
namespace Lifecycle
namespace Examples
namespace ImmutableCtor

def importedSourceName : String := "ImmutableCtor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ImmutableCtor"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "limit",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.immutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "y",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "limit0", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "limit") AssignOp.assign (Expr.ident "limit0")), Stmt.expr (Expr.assign (Expr.ident "y") AssignOp.assign (Expr.binary BinaryOp.add (Expr.ident "limit0") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "limit"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ImmutableCtor
end Examples
end Lifecycle
end Verify
