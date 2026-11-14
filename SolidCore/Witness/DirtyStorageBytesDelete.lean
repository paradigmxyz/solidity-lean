import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace DirtyStorageBytesDelete

def importedSourceName : String := "spec-hunt/87aeea6b.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "D"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "b",
    ty := Ty.bytes,
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.nonpayable,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "b")), Stmt.returnValues (some (Expr.literal (Literal.number "1")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end DirtyStorageBytesDelete
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.DirtyStorageBytesDelete
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev D := SolidCore.Solidity.SolcAstImport.DirtyStorageBytesDelete.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 4096 D "run" (State.empty.storeSlot 0 3) [] 34)
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 4096 D "run" (State.empty.storeSlot 0 64) [] 34)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 D "run" (State.empty.storeSlot 0 2) [] 1)
#guard isOkTrue (do
  let state ← Examples.checkedOwnCallState 4096 D "run" (State.empty.storeSlot 0 2) []
  pure (wordEq (state.loadSlot 0) 0))
end SolidCore.Solidity.Witness.DirtyStorageBytesDelete
