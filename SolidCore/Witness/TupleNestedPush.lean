import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked
set_option maxHeartbeats 8000000
namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace TupleNestedPush

def importedSourceName : String := "spec-hunt/8ea1f69d.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.stateVar
  { name := "values",
    ty := Ty.array (Ty.array (Ty.uint 256) (none)) (none),
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
    body := some (Stmt.block [Stmt.expr (Expr.call (Expr.member (Expr.ident "values") "push") []), Stmt.expr (Expr.assign (Expr.tuple [TupleItem.value (Expr.call (Expr.member (Expr.index (Expr.ident "values") (Expr.literal (Literal.number "0"))) "push") []), TupleItem.hole]) AssignOp.assign (Expr.tuple [TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "7"))]), TupleItem.value (Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional (Expr.literal (Literal.number "0"))])])), Stmt.returnValues (some (Expr.index (Expr.index (Expr.ident "values") (Expr.literal (Literal.number "0"))) (Expr.literal (Literal.number "0"))))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end TupleNestedPush
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore.Solidity.Witness.TupleNestedPush
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck
abbrev C := SolidCore.Solidity.SolcAstImport.TupleNestedPush.importedContract
private def isOkTrue : Except TypeError Bool -> Bool
  | .ok true => true
  | _ => false
#guard SolidCore.Solidity.SolcAstImport.TupleNestedPush.importedContractAccepted
#guard isOkTrue (Examples.checkedOwnCallWordAndSlotMatches 4096 C "run" State.empty [] 7 1)
end SolidCore.Solidity.Witness.TupleNestedPush
