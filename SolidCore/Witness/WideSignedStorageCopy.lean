import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
set_option maxHeartbeats 8000000
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace WideSignedStorageCopy

def importedSourceName : String := "spec-hunt/2e8d613b.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "s",
    ty := Ty.array (Ty.int 184) (some 1),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "d",
    ty := Ty.array (Ty.int 184) (some 1),
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
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.index (Expr.ident "s") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.unary UnaryOp.neg (Expr.literal (Literal.number "1")))), Stmt.expr (Expr.assign (Expr.ident "d") AssignOp.assign (Expr.ident "s")), Stmt.returnValues (some (Expr.index (Expr.ident "d") (Expr.literal (Literal.number "0"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end WideSignedStorageCopy
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.WideSignedStorageCopy
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.WideSignedStorageCopy.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
private def destinationClean (initial : State) : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 C "run" initial []
  Except.ok (wordEq (state.loadSlot 1) (2 ^ 184 - 1))
#guard SolidCore.Solidity.SolcAstImport.WideSignedStorageCopy.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallIntMatches 4096 C "run" State.empty [] (SolidCore.Solidity.Shared.signedToWord (-1)))
#guard isOkTrue (destinationClean State.empty)
#guard isOkTrue (destinationClean (State.empty.storeSlot 1 (0x123456789abcdef123 * 2 ^ 184)))
end SolidCore.Solidity.Witness.WideSignedStorageCopy
