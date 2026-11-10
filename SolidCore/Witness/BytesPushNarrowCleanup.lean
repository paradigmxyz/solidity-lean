import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Narrow checked arithmetic in the value of a storage `bytes` push must run at
its operand width. With `uint8 x = 200`, `bs.push(bytes1(x + 100))` reverts
Panic(0x11) before pushing, both on the state variable and through a
`bytes storage` reference; `x = 1` pushes the byte 0x65.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace BytesPushNarrowCleanup

def importedSourceName : String := "BytesPushNarrowCleanup.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "bs",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "bs") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))])]), Stmt.returnValues (some (Expr.member (Expr.ident "bs") "length"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "x", ty := Ty.uint 8, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "r", ty := Ty.bytes, location := some DataLocation.storage }] (some (Expr.ident "bs")), Stmt.expr (Expr.call (Expr.member (Expr.ident "r") "push") [Arg.positional (Expr.call (Expr.typeName (Ty.bytesN 1)) [Arg.positional (Expr.binary BinaryOp.add (Expr.ident "x") (Expr.literal (Literal.number "100")))])]), Stmt.returnValues (some (Expr.call (Expr.typeName (Ty.uint 8)) [Arg.positional (Expr.index (Expr.ident "r") (Expr.binary BinaryOp.sub (Expr.member (Expr.ident "r") "length") (Expr.literal (Literal.number "1"))))]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.28", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end BytesPushNarrowCleanup
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.BytesPushNarrowCleanup

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C := SolidCore.Solidity.SolcAstImport.BytesPushNarrowCleanup.importedContract

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard SolidCore.Solidity.SolcAstImport.BytesPushNarrowCleanup.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "f" State.empty [Value.word 200] 17)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 1024 C "g" State.empty [Value.word 200] 17)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "f" State.empty [Value.word 1] 1)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 1024 C "g" State.empty [Value.word 1] 101)

end SolidCore.Solidity.Witness.BytesPushNarrowCleanup
