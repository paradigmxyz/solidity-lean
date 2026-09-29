import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
An inline fixed array literal can initialize a dynamic storage array. Its
elements must be lowered at the storage destination's base type, including
signed negative literals: `int16[] x = [-1, -2]` deploys with two elements and
`x[0] + x[1] == -3`.
-/

namespace SolidCore.Solidity.Witness.DynamicStorageNegativeArrayInit

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def neg (s : String) : Expr := Expr.unary UnaryOp.neg (num s)

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.view
    params := []
    returns := [{ name := none, ty := Ty.int 16, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block
      [ Stmt.returnValues
          (some (Expr.binary BinaryOp.add
            (Expr.index (Expr.ident "x") (num "0"))
            (Expr.index (Expr.ident "x") (num "1")))) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "Test"
    abstract := false
    bases := []
    items :=
      [ ContractItem.stateVar
          { name := "x"
            ty := Ty.array (Ty.int 16) none
            visibility := some Visibility.public_
            mutability := VarMutability.mutable
            override? := none
            init := some (Expr.array [neg "1", neg "2"]) }
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

def deployedState : Except TypeError State :=
  Examples.checkedConstructState 4096 sourceUnit "Test" []

def sumIsNegThree : Except TypeError Bool := do
  let state ← deployedState
  Examples.checkedCallWordMatches 4096 sourceUnit "Test" "run" state []
    (SolidCore.Solidity.Shared.signedToWord (-3))

#guard accepted
#guard isOkTrue sumIsNegThree

end SolidCore.Solidity.Witness.DynamicStorageNegativeArrayInit
