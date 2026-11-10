import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Narrow checked arithmetic around an internal call keeps its operand-width
check when another operator consumes it: `uint32(g()) * uint32(100000)`
(10^10 > 2^32) reverts Panic(0x11) under `&` in a multi-value return and
under a comparison. With `h() = 1000` the product 10^6 is masked to 16960.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleReturnCallBitAndNarrow

def importedSourceName : String := "TupleReturnCallBitAndNarrow.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "100000")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "h",
    visibility := some Visibility.internal_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.literal (Literal.number "1000")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.bitAnd (Expr.binary BinaryOp.mul (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.ident "g") [])]) (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "100000"))])) (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "184"))])), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "cmp",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }, { name := none, ty := Ty.uint 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.gt (Expr.binary BinaryOp.mul (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.ident "g") [])]) (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "100000"))])) (Expr.literal (Literal.number "5"))), TupleItem.value (Expr.literal (Literal.number "1"))]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "safe",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 32, location := none }, { name := none, ty := Ty.uint 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.tuple [TupleItem.value (Expr.binary BinaryOp.bitAnd (Expr.binary BinaryOp.mul (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.call (Expr.ident "h") [])]) (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "1000"))])) (Expr.call (Expr.typeName (Ty.uint 32)) [Arg.positional (Expr.literal (Literal.number "0xffff"))])), TupleItem.value (Expr.literal (Literal.number "1"))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleReturnCallBitAndNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.TupleReturnCallBitAndNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.TupleReturnCallBitAndNarrow.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.TupleReturnCallBitAndNarrow.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "cmp" State.empty [] 17)
#guard isOkTrue (Examples.checkedOwnCallWordPairMatches 1024 C "safe" State.empty [] 16960 1)

end SolidCore.Solidity.Witness.TupleReturnCallBitAndNarrow
