-- Generated from scripts/refinement/bank/bank.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace Bank

def importedSourceName : String := "scripts/refinement/bank/bank.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Bank"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "balances",
    ty := Ty.mapping (Ty.address false) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "total",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.eventDecl
  { name := "Deposit",
    params := [{ name := some "who", ty := Ty.address false, indexed := true }, { name := some "amount", ty := Ty.uint 256, indexed := false }],
    anonymous := false }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "credit",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "who", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "balances") (Expr.ident "who")) AssignOp.addAssign (Expr.ident "amount")), Stmt.expr (Expr.assign (Expr.ident "total") AssignOp.addAssign (Expr.ident "amount")), Stmt.returnValues (some (Expr.index (Expr.ident "balances") (Expr.ident "who")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "deposit",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.ident "credit") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "amount")])), Stmt.emitEvent (Expr.call (Expr.ident "Deposit") [Arg.positional (Expr.member (Expr.ident "msg") "sender"), Arg.positional (Expr.ident "amount")]), Stmt.returnValues (some (Expr.ident "b"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "depositFor",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "who", ty := Ty.address false, location := none }, { name := some "amount", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "credit") [Arg.positional (Expr.ident "who"), Arg.positional (Expr.ident "amount")]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "balanceOf",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "who", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "balances") (Expr.ident "who")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end Bank
end Source
end Refinement
end SolidCore
