import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace SignedArrayMemberCopy

def importedSourceName : String := "spec-hunt/d5e1e2ff.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "a", ty := Ty.array (Ty.int 184) (some 1) }] }), (ContractItem.stateVar
  { name := "x",
    ty := Ty.user ({ segments := ["S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "y",
    ty := Ty.user ({ segments := ["S"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.int 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.member (Expr.ident "x") "a") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.assign (Expr.member (Expr.ident "y") "a") AssignOp.assign (Expr.member (Expr.ident "x") "a")), Stmt.returnValues (some (Expr.index (Expr.member (Expr.ident "y") "a") (Expr.literal (Literal.number "0"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end SignedArrayMemberCopy
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.SignedArrayMemberCopy
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.SignedArrayMemberCopy.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard isOkTrue (Examples.checkedOwnCallIntMatches 4096 C "run" State.empty [] (SolidCore.Solidity.Shared.signedToWord (-1)))
#guard isOkTrue (do
  let state ← Examples.checkedOwnCallState 4096 C "run" State.empty []
  pure (wordEq (state.loadSlot 1) (2^184-1)))
end SolidCore.Solidity.Witness.SignedArrayMemberCopy
