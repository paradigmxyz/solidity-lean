-- Generated from Contracts/CallFamilies/Calls.sol with solc 0.8.35 by scripts/solc_ast_to_lean_source.py. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Verify
namespace VC
namespace Source
namespace Calls

def importedSourceName : String := "Contracts/CallFamilies/Calls.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.interface
  name := "IBalance"
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
{ kind := ContractKind.interface
  name := "IFeeTo"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "feeTo",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := none })] }

def importedContractDecl2 : ContractDecl :=
{ kind := ContractKind.interface
  name := "ICallback"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "onFlash",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "sender", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }, { name := some "data", ty := Ty.bytes, location := some DataLocation.calldata }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := none })] }

def importedContractDecl3 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Calls"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "TRANSFER",
    ty := Ty.bytesN 4,
    visibility := some Visibility.private_,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.typeName (Ty.bytes)) [Arg.positional (Expr.literal (Literal.string "transfer(address,uint256)"))])])]) }), (ContractItem.stateVar
  { name := "factory",
    ty := Ty.address false,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "token",
    ty := Ty.address false,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "reserve",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "kLast",
    ty := Ty.uint 256,
    visibility := some Visibility.public_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pay",
    visibility := some Visibility.private_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "ok", ty := Ty.bool, location := none }, { name := some "ret", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "token") "call") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") [Arg.positional (Expr.ident "TRANSFER"), Arg.positional (Expr.ident "to"), Arg.positional (Expr.ident "amount")])])), Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.boolAnd (Expr.ident "ok") (Expr.binary BinaryOp.boolOr (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "ret") "length") (Expr.literal (Literal.number "0"))) (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.ident "ret"), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.bool))])]))), Arg.positional (Expr.literal (Literal.string "TRANSFER_FAILED"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "sync",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "reserve") AssignOp.assign (Expr.call (Expr.member (Expr.call (Expr.typeName (Ty.user ({ segments := ["IBalance"] }))) [Arg.positional (Expr.ident "token")]) "balanceOf") [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.ident "this")])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "skim",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "pay") [Arg.positional (Expr.ident "to"), Arg.positional (Expr.binary BinaryOp.sub (Expr.call (Expr.member (Expr.call (Expr.typeName (Ty.user ({ segments := ["IBalance"] }))) [Arg.positional (Expr.ident "token")]) "balanceOf") [Arg.positional (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.ident "this")])]) (Expr.ident "reserve"))])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "feeOn",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := some "on", ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "on") AssignOp.assign (Expr.binary BinaryOp.ne (Expr.call (Expr.member (Expr.call (Expr.typeName (Ty.user ({ segments := ["IFeeTo"] }))) [Arg.positional (Expr.ident "factory")]) "feeTo") []) (Expr.call (Expr.typeName (Ty.address false)) [Arg.positional (Expr.literal (Literal.number "0"))]))), Stmt.ifElse (Expr.ident "on") (Stmt.expr (Expr.assign (Expr.ident "kLast") AssignOp.assign (Expr.literal (Literal.number "1")))) none]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "flash",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }, { name := some "data", ty := Ty.bytes, location := some DataLocation.calldata }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "pay") [Arg.positional (Expr.ident "to"), Arg.positional (Expr.ident "amount")]), Stmt.ifElse (Expr.binary BinaryOp.gt (Expr.member (Expr.ident "data") "length") (Expr.literal (Literal.number "0"))) (Stmt.expr (Expr.call (Expr.member (Expr.call (Expr.typeName (Ty.user ({ segments := ["ICallback"] }))) [Arg.positional (Expr.ident "to")]) "onFlash") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "amount"), Arg.positional (Expr.ident "data")])) none]) })] }

def importedContract : ContractDecl :=
  importedContractDecl3

def importedContracts : List ContractDecl :=
  [importedContractDecl0, importedContractDecl1, importedContractDecl2, importedContractDecl3]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0, SourceItem.contract importedContractDecl1, SourceItem.contract importedContractDecl2, SourceItem.contract importedContractDecl3] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Calls
end Source
end VC
end Verify
end SolidCore
