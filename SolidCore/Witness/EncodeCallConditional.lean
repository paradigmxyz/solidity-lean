import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
set_option maxHeartbeats 8000000

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EncodeCallConditional

def importedSourceName : String := "spec-hunt/9186cd61.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "first",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "value", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.ident "value"))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "second",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "value", ty := Ty.uint 256, location := none }],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "value") (Expr.literal (Literal.number "1"))))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "chooseFirst", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.bytes, location := some DataLocation.memory }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.member (Expr.ident "abi") "encodeCall") [Arg.positional (Expr.ternary (Expr.ident "chooseFirst") (Expr.member (Expr.ident "this") "first") (Expr.member (Expr.ident "this") "second")), Arg.positional (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "9"))])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EncodeCallConditional
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.EncodeCallConditional
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.EncodeCallConditional.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
private def expected (signature : String) : List Nat :=
  wordToBytesBE 4 (ABI.selectorFromSignature signature) ++ wordToBytesBE 32 9
#guard SolidCore.Solidity.SolcAstImport.EncodeCallConditional.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallBytesMatches 4096 C "run" State.empty
  [Value.word 1] (expected "first(uint256)"))
#guard isOkTrue (Examples.checkedOwnCallBytesMatches 4096 C "run" State.empty
  [Value.word 0] (expected "second(uint256)"))
end SolidCore.Solidity.Witness.EncodeCallConditional
