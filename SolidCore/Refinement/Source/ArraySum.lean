-- Generated from scripts/refinement/mem/array_sum.sol with solc 0.8.35 the way scripts/refinement/gen.sh writes Source/NAME.lean. Do not edit.

import SolidCore.Solidity.Checked

open SolidCore.Solidity

namespace SolidCore
namespace Refinement
namespace Source
namespace ArraySum

def importedSourceName : String := "scripts/refinement/mem/array_sum.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "ArraySum"
  abstract := false
  bases := []
  items := [(ContractItem.function
  { kind := FunctionKind.function,
    name := some "sum",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [{ name := some "xs", ty := Ty.array (Ty.uint 256) (none), location := some DataLocation.calldata }],
    returns := [{ name := some "s", ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.forLoop (some (Stmt.varDecl [{ name := some "i", ty := Ty.uint 256, location := none }] (some (Expr.literal (Literal.number "0"))))) (some (Expr.binary BinaryOp.lt (Expr.ident "i") (Expr.member (Expr.ident "xs") "length"))) (some (Expr.unary UnaryOp.postIncrement (Expr.ident "i"))) (Stmt.block [Stmt.expr (Expr.assign (Expr.ident "s") AssignOp.addAssign (Expr.index (Expr.ident "xs") (Expr.ident "i")))])]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.0", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end ArraySum
end Source
end Refinement
end SolidCore
