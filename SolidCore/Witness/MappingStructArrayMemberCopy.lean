import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
Selecting a dynamic-array member of a fixed storage-array element must resolve
the complete path before materializing the value. Loading the intermediate
struct as a whole is invalid when it also contains a mapping, even though the
selected dynamic-array field itself is freely copyable to memory.
-/

namespace SolidCore.Solidity.Witness.MappingStructArrayMemberCopy

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)

private def boxPath : Path := { segments := ["Box"] }
private def boxTy : Ty := Ty.user boxPath

private def boxDecl : StructDecl :=
  { name := "Box"
    fields :=
      [ { name := "words", ty := Ty.array (Ty.uint 256) none }
      , { name := "other", ty := Ty.mapping (Ty.uint 256) (Ty.uint 256) } ] }

private def boxesZeroWords : Expr :=
  Expr.member (Expr.index (Expr.ident "boxes") (num "0")) "words"

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    params := []
    returns := [{ name := none, ty := Ty.uint 256, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block
      [ Stmt.expr
          (Expr.call (Expr.member boxesZeroWords "push")
            [Arg.positional (num "18")])
      , Stmt.varDecl
          [{ name := some "copied", ty := some (Ty.array (Ty.uint 256) none),
             location := some DataLocation.memory }]
          (some boxesZeroWords)
      , Stmt.returnValues
          (some (Expr.index (Expr.ident "copied") (num "0"))) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.structDecl boxDecl
      , ContractItem.stateVar
          { name := "boxes"
            ty := Ty.array boxTy (some 1)
            visibility := some Visibility.internal_
            mutability := VarMutability.mutable
            override? := none
            init := none }
      , ContractItem.function runFn ] }

def sourceUnit : SourceUnit :=
  { items :=
      [ SourceItem.pragma "solidity" "0.8.35"
      , SourceItem.contract contract ] }

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

end SolidCore.Solidity.Witness.MappingStructArrayMemberCopy
