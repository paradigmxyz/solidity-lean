-- Generated from scripts/refinement/mem/safe_transfer.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace SafeTransfer

def importedSourceName : String := "scripts/refinement/mem/safe_transfer.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "SafeTransfer"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "SELECTOR",
    ty := Ty.bytesN 4,
    visibility := some Visibility.private_,
    mutability := VarMutability.constant,
    override? := none,
    init := some (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.typeName (Ty.bytes)) [Arg.positional (Expr.literal (Literal.string "transfer(address,uint256)"))])])]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "pay",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "token", ty := Ty.address false, location := none }, { name := some "to", ty := Ty.address false, location := none }, { name := some "value", ty := Ty.uint 256, location := none }],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "success", ty := Ty.bool, location := none }, { name := some "data", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "token") "call") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodeWithSelector") [Arg.positional (Expr.ident "SELECTOR"), Arg.positional (Expr.ident "to"), Arg.positional (Expr.ident "value")])])), Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.boolAnd (Expr.ident "success") (Expr.binary BinaryOp.boolOr (Expr.binary BinaryOp.eq (Expr.member (Expr.ident "data") "length") (Expr.literal (Literal.number "0"))) (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.ident "data"), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.bool))])]))), Arg.positional (Expr.literal (Literal.string "TRANSFER_FAILED"))])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SafeTransfer
end Source
end Refinement
end SolidCore
