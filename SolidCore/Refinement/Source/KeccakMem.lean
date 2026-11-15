-- Generated from scripts/refinement/mem/keccak_mem.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace KeccakMem

def importedSourceName : String := "scripts/refinement/mem/keccak_mem.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "KeccakMem"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "salt",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "token0", ty := Ty.address false, location := none }, { name := some "token1", ty := Ty.address false, location := none }],
    returns := [{ name := none, ty := Ty.bytesN 32, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.returnValues (some (Expr.call (Expr.ident "keccak256") [Arg.positional (Expr.call (Expr.member (Expr.ident "abi") "encodePacked") [Arg.positional (Expr.ident "token0"), Arg.positional (Expr.ident "token1")])]))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end KeccakMem
end Source
end Refinement
end SolidCore
