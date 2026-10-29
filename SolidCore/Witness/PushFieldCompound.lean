import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
set_option maxHeartbeats 8000000
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace PushFieldCompound

def importedSourceName : String := "spec-hunt/bcf19b5e.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "Item",
    fields := [{ name := "value", ty := Ty.uint 256 }] }), (ContractItem.stateVar
  { name := "values",
    ty := Ty.array (Ty.user ({ segments := ["Item"] })) (none),
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
    body := some (Stmt.block [Stmt.expr (Expr.assign (Expr.member (Expr.call (Expr.member (Expr.ident "values") "push") []) "value") AssignOp.addAssign (Expr.literal (Literal.number "7"))), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "values") (Expr.literal (Literal.number "0"))) "value"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end PushFieldCompound
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.PushFieldCompound
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.PushFieldCompound.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard SolidCore.Solidity.SolcAstImport.PushFieldCompound.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallWordAndSlotMatches 4096 C "run" State.empty [] 7 1)
end SolidCore.Solidity.Witness.PushFieldCompound
