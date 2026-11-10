import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
The data of a multi-value `abi.decode` keeps its narrow checked arithmetic in
both tuple declarations and tuple assignments: `abi.encode(x + 100, 1)` with
`uint8 x = 200` reverts Panic(0x11). With `x = 1` it decodes 101 and 1.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleDecodeNarrow

def importedSourceName : String := "TupleDecodeNarrow.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100"))), Arg.positional (Expr.literal (Literal.number "1"))]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 256)), TupleItem.value (Expr.typeName (Ty.uint 256))])])), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]) AssignOp.assign (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100"))), Arg.positional (Expr.literal (Literal.number "1"))]), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.uint 256)), TupleItem.value (Expr.typeName (Ty.uint 256))])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleDecodeNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.TupleDecodeNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.TupleDecodeNarrow.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.TupleDecodeNarrow.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [Value.word 200] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "g" State.empty [Value.word 200] 17)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "f" State.empty [Value.word 1] 102)
#guard isOkTrue (Examples.checkedOwnCallWordPairMatches 1024 C "g" State.empty [Value.word 1] 101 1)

end SolidCore.Solidity.Witness.TupleDecodeNarrow
