import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
set_option maxHeartbeats 8000000

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace ConditionalFunctionMembers

def importedSourceName : String := "tests/forge-harness/conditional-function-members/src/ConditionalFunctionMembers.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ConditionalFunctionMembers"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block []) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "g",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block []) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "selectorMatches",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [{ name := some "choose", ty := Ty.bool, location := none }],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "expected", ty := Ty.bytesN 4, location := none }] (some (Expr.ternary (Expr.ident "choose") (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.literal (Literal.number "0x26121ff0"))]) (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.literal (Literal.number "0xe2179b8e"))]))), Stmt.returnValues (some (Expr.binary BinaryOp.eq (Expr.member (Expr.ternary (Expr.ident "choose") (Expr.member (Expr.ident "this") "f") (Expr.member (Expr.ident "this") "g")) "selector") (Expr.ident "expected")))]) }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "namedSelectorPure",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.bool, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.binary BinaryOp.eq (Expr.member (Expr.member (Expr.ident "this") "f") "selector") (Expr.call (Expr.typeName (Ty.bytesN 4)) [Arg.positional (Expr.literal (Literal.number "0x26121ff0"))])))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ConditionalFunctionMembers
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.ConditionalFunctionMembers
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.ConditionalFunctionMembers.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard SolidCore.Solidity.SolcAstImport.ConditionalFunctionMembers.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallWordMatches 256 C "selectorMatches" State.empty [.word 1] 1)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 256 C "selectorMatches" State.empty [.word 0] 1)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 256 C "namedSelectorPure" State.empty [] 1)
end SolidCore.Solidity.Witness.ConditionalFunctionMembers
