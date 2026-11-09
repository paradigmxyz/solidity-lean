import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace EnumMappingKeyContract

def importedSourceName : String := "spec-hunt/9c40b86d.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.enumDecl
  { name := "E",
    cases := ["A", "B", "C"] }), (ContractItem.stateVar
  { name := "x",
    ty := Ty.user ({ segments := ["E"] }),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.stateVar
  { name := "m",
    ty := Ty.mapping (Ty.user ({ segments := ["E"] })) (Ty.uint 256),
    visibility := some Visibility.internal_,
    mutability := VarMutability.mutable,
    override? := none,
    init := none }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.external_,
    mutability := StateMutability.view,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.index (Expr.ident "m") (Expr.ident "x")))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end EnumMappingKeyContract
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.EnumMappingKeyContract
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.EnumMappingKeyContract.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard SolidCore.Solidity.SolcAstImport.EnumMappingKeyContract.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallPanicMatches 4096 C "run" (State.empty.storeSlot 0 5) [] 33)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 C "run" State.empty [] 0)
#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 C "run" (State.empty.storeSlot 0 2) [] 0)
end SolidCore.Solidity.Witness.EnumMappingKeyContract
