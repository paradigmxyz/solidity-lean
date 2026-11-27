import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ModularArgumentOrder

def importedSourceName : String := "spec-hunt/8382b6f4.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "2")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "addmod") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n"), Arg.positional (Expr.literal (Literal.number "100"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ModularArgumentOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.ModularArgumentOrder
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.ModularArgumentOrder.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 C "f" (State.empty.storeSlot 0 2) [] 5)
#guard isOkTrue (do
  let state ← Examples.checkedOwnCallState 4096 C "f" (State.empty.storeSlot 0 2) []
  pure (wordEq (state.loadSlot 0) 3))
end SolidCore.Solidity.Witness.ModularArgumentOrder

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace MulmodArgumentOrder

def importedSourceName : String := "spec-hunt/8382b6f4.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "n",
    ty := Ty.uint 256,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := some (Expr.literal (Literal.number "2")) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "bump",
    visibility := some Visibility.internal_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (Expr.literal (Literal.number "1"))), Stmt.returnValues (some (Expr.ident "n"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "mulmod") [Arg.positional (Expr.call (Expr.ident "bump") []), Arg.positional (Expr.ident "n"), Arg.positional (Expr.literal (Literal.number "100"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end MulmodArgumentOrder
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.MulmodArgumentOrder
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.MulmodArgumentOrder.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 C "f" (State.empty.storeSlot 0 2) [] 6)
end SolidCore.Solidity.Witness.MulmodArgumentOrder
