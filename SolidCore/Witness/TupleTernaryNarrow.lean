import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A conditional of tuples on the right of a tuple assignment or declaration
keeps the narrow checked arithmetic of the selected branch: `x * 2` with
`uint16 x = 65535` reverts Panic(0x11). With `x = 3` it yields (6, 1).
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleTernaryNarrow

def importedSourceName : String := "TupleTernaryNarrow.sol"

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
    params := [{ name := some "x", ty := Ty.uint 16, location := none }],
    returns := [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.ident "a"), TupleItem.value (Expr.ident "b")]) AssignOp.assign (Expr.ternary (Expr.binary BinaryOp.gt (Expr.ident "x") (Expr.literal (Literal.number "0"))) (Expr.tuple [TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.literal (Literal.number "2")))]), TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "1"))])]) (Expr.tuple [TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))]), TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))])])))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.uint 256, location := none }, { name := some "b", ty := Ty.uint 256, location := none }] (some (Expr.ternary (Expr.binary BinaryOp.gt (Expr.ident "x") (Expr.literal (Literal.number "0"))) (Expr.tuple [TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.literal (Literal.number "2")))]), TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "1"))])]) (Expr.tuple [TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))]), TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))])]))), Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "b")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleTernaryNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.TupleTernaryNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.TupleTernaryNarrow.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.TupleTernaryNarrow.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [Value.word 65535] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "g" State.empty [Value.word 65535] 17)
#guard isOkTrue (Examples.checkedOwnCallWordPairMatches 1024 C "f" State.empty [Value.word 3] 6 1)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "g" State.empty [Value.word 3] 7)

end SolidCore.Solidity.Witness.TupleTernaryNarrow
