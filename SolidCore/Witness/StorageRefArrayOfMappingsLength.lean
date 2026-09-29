import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
STORAGE-REF ARRAY-OF-MAPPINGS LENGTH (#049e7d8e): `.length` on a storage
reference must read the array header without materializing its elements.

The failing shape is a dynamic array of dynamic arrays of mappings.  After
binding the inner array to `b` and pushing a mapping element, evaluating
`b.length - 1` used to load the whole inner array.  Mappings have no Solidity
value representation, so that load failed with `typeMismatch` / Panic(0), even
though the length read and the subsequent mapping write are valid.
-/

namespace SolidCore
namespace Solidity
namespace SolcAstImport
namespace StorageRefArrayOfMappingsLength

open SolidCore.Solidity.Source

private def one : Expr := Expr.literal (Literal.number "1")
private def aLength : Expr := Expr.member (Expr.ident "a") "length"
private def bLength : Expr := Expr.member (Expr.ident "b") "length"
private def last (length : Expr) : Expr :=
  Expr.binary BinaryOp.sub length one

private def innerTy : Ty :=
  Ty.array (Ty.mapping (Ty.uint 256) (Ty.uint 256)) none

private def runFn : ContractItem := ContractItem.function
  { kind := FunctionKind.function,
    name := some "run",
    visibility := some Visibility.public_,
    mutability := StateMutability.nonpayable,
    params := [{ name := some "key", ty := Ty.uint 256 },
               { name := some "value", ty := Ty.uint 256 }],
    returns := [{ name := none, ty := Ty.uint 256 }],
    body := some (Stmt.block
      [ Stmt.expr (Expr.call (Expr.member (Expr.ident "a") "push") [])
      , Stmt.varDecl
          [{ name := some "b", ty := innerTy,
             location := some DataLocation.storage }]
          (some (Expr.index (Expr.ident "a") (last aLength)))
      , Stmt.expr (Expr.call (Expr.member (Expr.ident "b") "push") [])
      , Stmt.expr (Expr.assign
          (Expr.index
            (Expr.index (Expr.ident "b") (last bLength))
            (Expr.ident "key"))
          AssignOp.assign (Expr.ident "value"))
      , Stmt.returnValues (some
          (Expr.index
            (Expr.index (Expr.ident "b") (last bLength))
            (Expr.ident "key"))) ]) }

def importedContractDecl0 : ContractDecl :=
  { kind := ContractKind.contract,
    name := "C",
    items :=
      [ ContractItem.stateVar
          { name := "a", ty := Ty.array innerTy none }
      , runFn ] }

def importedContract : ContractDecl := importedContractDecl0
def importedContracts : List ContractDecl := [importedContractDecl0]
def importedSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract importedContractDecl0] }

def importedContractAccepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit importedSourceUnit)

end StorageRefArrayOfMappingsLength
end SolcAstImport
end Solidity
end SolidCore

namespace SolidCore
namespace Solidity
namespace Witness
namespace StorageRefArrayOfMappingsLength

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

abbrev C :=
  SolidCore.Solidity.SolcAstImport.StorageRefArrayOfMappingsLength.importedContract

def accepted : Bool :=
  SolidCore.Solidity.SolcAstImport.StorageRefArrayOfMappingsLength.importedContractAccepted

def run_42_64_returns_64 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 C "run" State.empty
    [Value.word 42, Value.word 64] 64

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_42_64_returns_64

end StorageRefArrayOfMappingsLength
end Witness
end Solidity
end SolidCore
