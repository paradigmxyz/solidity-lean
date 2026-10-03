import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Copying a dynamic-array member through a local storage alias must resolve the
complete storage path before reading. Evaluating the alias base by value tries
to materialize its enclosing struct, which is impossible when it has a mapping.
-/

namespace SolidCore.Solidity.Witness.StorageAliasArrayMemberMemoryCopy

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (n : String) : Expr := Expr.literal (Literal.number n)
private def arrayTy : Ty := Ty.array (Ty.uint 256) none
private def boxTy : Ty := Ty.user { segments := ["Box"] }
private def box0Words : Expr :=
  Expr.member (Expr.ident "box0") "words"

private def boxDecl : StructDecl :=
  { name := "Box"
    fields :=
      [ { name := "words", ty := arrayTy }
      , { name := "values", ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) } ] }

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.uint 256 }]
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "box0", ty := some boxTy,
             location := some DataLocation.storage }]
          (some (Expr.index (Expr.ident "boxes") (num "0")))
      , Stmt.expr (Expr.call (Expr.member box0Words "push")
          [Arg.positional (num "18")])
      , Stmt.varDecl
          [{ name := some "copied", ty := some arrayTy,
             location := some DataLocation.memory }]
          (some box0Words)
      , Stmt.returnValues
          (some (Expr.index (Expr.ident "copied") (num "0"))) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.structDecl boxDecl
      , ContractItem.stateVar
          { name := "boxes", ty := Ty.array boxTy (some 2) }
      , ContractItem.function runFn ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returnsEighteen : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty [] 18

#guard accepted
#guard isOkTrue returnsEighteen

end SolidCore.Solidity.Witness.StorageAliasArrayMemberMemoryCopy
