import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A `bytesN` conversion of `abi.encodePacked(...)` must keep the narrow
checked arithmetic of the packed arguments: `type(uint8).max + 1` and
`x + 100` with `uint8 x = 200` revert Panic(0x11). With `x = 1` the packed
byte 0x65 converts to the left-aligned `bytes32` word.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace BytesNFromEncodePackedNarrow

def importedSourceName : String := "BytesNFromEncodePackedNarrow.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "Main"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.member (Expr.typeName (Ty.uint 8)) "max") (Expr.literal (Literal.number "1")))])]))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.bytesN 32)) [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end BytesNFromEncodePackedNarrow
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.BytesNFromEncodePackedNarrow

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.BytesNFromEncodePackedNarrow.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.BytesNFromEncodePackedNarrow.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "g" State.empty [Value.word 200] 17)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "g" State.empty [Value.word 1] (101 * 2 ^ 248))

end SolidCore.Solidity.Witness.BytesNFromEncodePackedNarrow
