-- Generated from scripts/verify/Token.sol (solar-verify's crates/verify/examples/Token.sol) with solc 0.8.35 by scripts/solc_ast_to_lean_source.py. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Verify
namespace VC
namespace Source
namespace Token

def importedSourceName : String := "scripts/verify/Token.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Token"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "balanceOf",
    ty := Ty.mapping (Ty.address false) (Ty.uint 256),
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "totalSupply",
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
    init := none }), ContractItem.modifierDecl
  { name := "onlyOwner"
    params := []
    virtual := false
    override? := none
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "msg") "sender") (Expr.ident "owner")), Arg.positional (Expr.literal (Literal.string "not owner"))]), Stmt.modifierPlaceholder]) }, (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "owner") AssignOp.assign (Expr.member (Expr.ident "msg") "sender"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "mint",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [{ target := { segments := ["onlyOwner"] }, args := [], hasArgList := false }],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "totalSupply") AssignOp.addAssign (Expr.ident "amount")), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balanceOf") (Expr.ident "to")) AssignOp.addAssign (Expr.ident "amount"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "transfer",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "bal", ty := Ty.uint 256, location := none }] (some (Expr.index (Expr.ident "balanceOf") (Expr.member (Expr.ident "msg") "sender"))), Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.ge (Expr.ident "bal") (Expr.ident "amount")), Arg.positional (Expr.literal (Literal.string "insufficient"))]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balanceOf") (Expr.member (Expr.ident "msg") "sender")) AssignOp.assign (Expr.binary BinaryOp.sub (Expr.ident "bal") (Expr.ident "amount"))), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balanceOf") (Expr.ident "to")) AssignOp.addAssign (Expr.ident "amount")), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "burn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "balanceOf") (Expr.member (Expr.ident "msg") "sender")) AssignOp.subAssign (Expr.ident "amount")), Stmt.expr (Expr.assign (Expr.ident "totalSupply") AssignOp.subAssign (Expr.ident "amount"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.20", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Token
end Source
end VC
end Verify
end SolidCore
