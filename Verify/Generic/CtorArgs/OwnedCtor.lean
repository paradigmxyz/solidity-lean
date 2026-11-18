-- The solc-AST front end's output (scripts/solc_ast_to_lean_source.py, solc 0.8.30) for
-- Verify/Generic/CtorArgs/OwnedCtor.sol, under Verify.Generic.CtorArgs.OwnedCtor.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace Verify
namespace Generic
namespace CtorArgs
namespace OwnedCtor

def importedSourceName : String := "OwnedCtor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "OwnedCtor"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "x",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "owner",
    ty := Ty.address false,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "deployer",
    ty := Ty.address false,
    visibility := some Visibility.internal_,
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
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.ne (Expr.ident "x0") (Expr.literal (Literal.number "0")))]), Stmt.expr (Expr.assign (Expr.ident "x") AssignOp.assign (Expr.ident "x0")), Stmt.expr (Expr.assign (Expr.ident "owner") AssignOp.assign (Expr.ident "owner0")), Stmt.expr (Expr.assign (Expr.ident "deployer") AssignOp.assign (Expr.member (Expr.ident "msg") "sender"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "get",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.ifElse (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "msg") "sender") (Expr.ident "owner")) (Stmt.block [Stmt.returnValues (some (Expr.ident "x"))]) none, Stmt.returnValues (some (Expr.literal (Literal.number "0")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end OwnedCtor
end CtorArgs
end Generic
end Verify
