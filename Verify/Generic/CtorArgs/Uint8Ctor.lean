-- The solc-AST front end's output (scripts/solc_ast_to_lean_source.py, solc 0.8.30) for
-- Verify/Generic/CtorArgs/Uint8Ctor.sol, under Verify.Generic.CtorArgs.Uint8Ctor.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace Verify
namespace Generic
namespace CtorArgs
namespace Uint8Ctor

def importedSourceName : String := "Uint8Ctor.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Uint8Ctor"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "x",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.constructor,
    name := none,
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "v", ty := Ty.uint 8, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "x") AssignOp.assign (Expr.ident "v"))]) }), (ContractItem.function
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

end Uint8Ctor
end CtorArgs
end Generic
end Verify
