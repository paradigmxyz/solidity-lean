import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

/-!
ABI-DECODE-STRUCT-ARRAY — a contract-local struct's short and qualified paths
remain the same nominal type when nested inside an ABI decode array target.

The importer stores the declaration under both `S` and `C.S`. Before this fix,
ordinary array convertibility used raw `Ty` equality, so the decoded `C.S[]`
value could not initialize the source-declared `S[] memory d`; the accepted
program failed closed with `expectedType C.S[] S[]`. The checker now compares
identical array shapes recursively while recognizing only adjacent local aliases.
It still rejects element widening, contract covariance, and length changes in
ordinary array conversion contexts.

The source and expected result come from solc 0.8.35 and the EVM: encoding a
one-element `S[]`, decoding it, and reading `d[0].n` returns 7.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace AbiDecodeStructArray

def importedSourceName : String := "AbiDecodeStructArray.sol"

def importedContractDecl0 : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items := [(ContractItem.structDecl
  { name := "S",
    fields := [{ name := "n", ty := Ty.uint 256 }] }), (ContractItem.function
  { kind := FunctionKind.function,
    name := some "f",
    visibility := some Visibility.external_,
    mutability := StateMutability.pure,
    params := [],
    returns := [{ name := none, ty := Ty.uint 256, location := none }],
    virtual := false,
    override? := none,
    modifiers := [],
    body := some (Stmt.block [Stmt.varDecl [{ name := some "a", ty := Ty.array (Ty.user ({ segments := ["S"] })) (none), location := some DataLocation.memory }] (some (Expr.newExpr (Ty.array (Ty.user ({ segments := ["S"] })) (none)) [Arg.positional (Expr.literal (Literal.number "1"))])), Stmt.expr (Expr.assign (Expr.index (Expr.ident "a") (Expr.literal (Literal.number "0"))) AssignOp.assign (Expr.call (Expr.typeName (Ty.user ({ segments := ["S"] }))) [Arg.positional (Expr.literal (Literal.number "7"))])), Stmt.varDecl [{ name := some "e", ty := Ty.bytes, location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "abi") "encode") [Arg.positional (Expr.ident "a")])), Stmt.varDecl [{ name := some "d", ty := Ty.array (Ty.user ({ segments := ["S"] })) (none), location := some DataLocation.memory }] (some (Expr.call (Expr.member (Expr.ident "abi") "decode") [Arg.positional (Expr.ident "e"), Arg.positional (Expr.tuple [TupleItem.value (Expr.typeName (Ty.array (Ty.user ({ segments := ["S"] })) (none)))])])), Stmt.returnValues (some (Expr.member (Expr.index (Expr.ident "d") (Expr.literal (Literal.number "0"))) "n"))]) })] }

def importedContract : ContractDecl :=
  importedContractDecl0

def importedContracts : List ContractDecl :=
  [importedContractDecl0]

def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35", SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end AbiDecodeStructArray
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace AbiDecodeStructArray

open SolidCore.Solidity.TypeCheck
open SolidCore.Solidity.SolcAstImport.AbiDecodeStructArray

def accepted : Bool := importedContractAccepted

def runReturns7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 1024 importedContract "f"
    SolidCore.Solidity.Source.State.empty [] 7

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue runReturns7

end AbiDecodeStructArray
end Witness
end Solidity
end SolidCore
