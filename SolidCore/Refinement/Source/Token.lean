-- Generated from scripts/refinement/token/token.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace Token

def importedSourceName : String := "scripts/refinement/token/token.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Token"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "balances",
    ty := Ty.mapping (Ty.address false) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "allowances",
    ty := Ty.mapping (Ty.address false) (Ty.mapping (Ty.address false) (Ty.uint 256)),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "frozen",
    ty := Ty.mapping (Ty.address false) (Ty.bool),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "totalSupply",
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
    init := none }), (ContractItem.eventDecl
  { name := "Transfer",
    params := [{ name := some "from", ty := Ty.address false, indexed := true }, { name := some "to", ty := Ty.address false, indexed := true }, { name := some "value", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.eventDecl
  { name := "Approval",
    params := [{ name := some "owner", ty := Ty.address false, indexed := true }, { name := some "spender", ty := Ty.address false, indexed := true }, { name := some "value", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "balanceOf",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "who", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "balances") (Expr.ident "who")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "allowance",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "holder", ty := Ty.address false, location := none }, { name := some "spender", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "allowances") (Expr.ident "holder")) (Expr.ident "spender")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "getOwner",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.address false, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "owner"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "isFrozen",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "who", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "frozen") (Expr.ident "who")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "freeze",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "who", ty := Ty.address false, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "msg") "sender") (Expr.ident "owner"))]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "frozen") (Expr.ident "who")) AssignOp.assign (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "transfer",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "to", ty := Ty.address false, location := none }, { name := some "value", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.unary UnaryOp.logicalNot (Expr.index (Expr.ident "frozen") (Expr.member (Expr.ident "msg") "sender")))]), Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.ge (Expr.index (Expr.ident "balances") (Expr.member (Expr.ident "msg") "sender")) (Expr.ident "value")), Arg.positional (Expr.literal (Literal.string "balance"))]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balances") (Expr.member (Expr.ident "msg") "sender")) AssignOp.subAssign (Expr.ident "value")), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balances") (Expr.ident "to")) AssignOp.addAssign (Expr.ident "value")), Stmt.emitEvent (Expr.call (Expr.ident "Transfer") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "to"), Arg.positional (Expr.ident "value")]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "approve",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "spender", ty := Ty.address false, location := none }, { name := some "value", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "allowances") (Expr.member (Expr.ident "msg") "sender")) (Expr.ident "spender")) AssignOp.assign (Expr.ident "value")), Stmt.emitEvent (Expr.call (Expr.ident "Approval") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "spender"), Arg.positional (Expr.ident "value")]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "transferFrom",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "from", ty := Ty.address false, location := none }, { name := some "to", ty := Ty.address false, location := none }, { name := some "value", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }] (some (Expr.index (Expr.index (Expr.ident "allowances") (Expr.ident "from")) (Expr.member (Expr.ident "msg") "sender"))), Stmt.ifElse (Expr.binary BinaryOp.lt (Expr.ident "a") (Expr.ident "value")) (Stmt.block [Stmt.expr (Expr.call (Expr.ident "revert") [Arg.positional (Expr.literal (Literal.string "allowance"))])]) (some (Stmt.ifElse (Expr.binary BinaryOp.ne (Expr.ident "a") (Expr.member (Expr.typeName (Ty.uint 256)) "max")) (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.index (Expr.ident "allowances") (Expr.ident "from")) (Expr.member (Expr.ident "msg") "sender")) AssignOp.assign (Expr.binary BinaryOp.sub (Expr.ident "a") (Expr.ident "value")))]) none)), Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.ge (Expr.index (Expr.ident "balances") (Expr.ident "from")) (Expr.ident "value"))]), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balances") (Expr.ident "from")) AssignOp.subAssign (Expr.ident "value")), Stmt.expr (Expr.assign (Expr.index (Expr.ident "balances") (Expr.ident "to")) AssignOp.addAssign (Expr.ident "value")), Stmt.emitEvent (Expr.call (Expr.ident "Transfer") [Arg.positional (Expr.ident "from"), Arg.positional (Expr.ident "to"), Arg.positional (Expr.ident "value")]), Stmt.returnValues (some (Expr.literal (Literal.bool true)))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Token
end Source
end Refinement
end SolidCore
