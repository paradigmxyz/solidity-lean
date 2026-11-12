-- Generated from scripts/refinement/mulx/mul.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace MulX

def importedSourceName : String := "scripts/refinement/mulx/mul.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Main"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "x8",
    ty := Ty.uint 8,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "y16",
    ty := Ty.uint 16,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "3")) }), (ContractItem.stateVar
  { name := "z",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "m",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 16, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "x8") AssignOp.mulAssign (Expr.ident "a")), Stmt.expr (Expr.assign (Expr.ident "y16") AssignOp.mulAssign (Expr.ident "b"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "n",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "a", ty := Ty.uint 8, location := none }, { name := some "b", ty := Ty.uint 16, location := none }, { name := some "c", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "z") AssignOp.assign (Expr.binary BinaryOp.mul (Expr.binary BinaryOp.mul (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.ident "a")]) (Expr.ident "b")) (Expr.ident "c"))), Stmt.returnValues (some (Expr.ident "z"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end MulX
end Source
end Refinement
end SolidCore
