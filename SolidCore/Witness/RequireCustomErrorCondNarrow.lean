import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
The condition of `require(cond, E(...))` keeps its narrow checked arithmetic:
`x * 2` with `uint16 x = 65535` reverts Panic(0x11), with or without error
arguments. With `x = 3` the condition holds and the call returns.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace RequireCustomErrorCondNarrow

def importedSourceName : String := "RequireCustomErrorCondNarrow.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.errorDecl
  { name := "E",
    params := [] }), (ContractItem.errorDecl
  { name := "F",
    params := [{ name := some "v", ty := Ty.uint 256, location := none }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.gt (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.literal (Literal.number "2"))) (Expr.literal (Literal.number "0"))), Arg.positional (Expr.call (Expr.ident "E") [])]), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 16, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.ident "require") [Arg.positional (Expr.binary BinaryOp.gt (Expr.binary BinaryOp.mul (Expr.ident "x") (Expr.literal (Literal.number "2"))) (Expr.literal (Literal.number "0"))), Arg.positional (Expr.call (Expr.ident "F") [Arg.positional (Expr.ident "x")])]), Stmt.returnValues (some (Expr.literal (Literal.number "2")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end RequireCustomErrorCondNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.RequireCustomErrorCondNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.RequireCustomErrorCondNarrow.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.RequireCustomErrorCondNarrow.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [Value.word 65535] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "g" State.empty [Value.word 65535] 17)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "f" State.empty [Value.word 3] 1)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "g" State.empty [Value.word 3] 2)

end SolidCore.Solidity.Witness.RequireCustomErrorCondNarrow
