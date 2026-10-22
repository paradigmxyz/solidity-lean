import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
`values.push().length` reads the length of the newly appended dynamic array,
while the outer storage array grows from zero to one element.
-/

namespace SolidCore.Solidity.Witness.PushReturnLength

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar
          { name := "values",
            ty := Ty.array (Ty.array (Ty.uint 256) none) none }
      , ContractItem.function
          { kind := FunctionKind.function
            name := some "run"
            visibility := some Visibility.external_
            mutability := StateMutability.nonpayable
            returns := [{ name := none, ty := Ty.uint 256 }]
            body := some (Stmt.block
              [Stmt.returnValues (some (Expr.member
                (Expr.call (Expr.member (Expr.ident "values") "push") [])
                "length"))]) } ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
      SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def returnMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty [] 0

def outerLengthMatches : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "run" State.empty []
  Except.ok (wordEq (state.loadSlot 0) 1)

#guard accepted
#guard isOkTrue returnMatches
#guard isOkTrue outerLengthMatches

def initializerContract : ContractDecl :=
  { contract with items :=
    [ ContractItem.stateVar
        { name := "values", ty := Ty.array (Ty.array (Ty.uint 256) none) none }
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.nonpayable
          returns := [{ name := none, ty := Ty.uint 256 }]
          body := some (Stmt.block
            [ Stmt.varDecl [{ name := some "length", ty := Ty.uint 256 }]
                (some (Expr.member
                  (Expr.call (Expr.member (Expr.ident "values") "push") []) "length"))
            , Stmt.returnValues (some (Expr.binary BinaryOp.add (Expr.ident "length")
                (Expr.member (Expr.ident "values") "length"))) ]) } ] }

#guard isOkTrue (Examples.checkedOwnCallWordMatches 4096 initializerContract
  "run" State.empty [] 1)
#guard isOkTrue (do
  let state ← Examples.checkedOwnCallState 4096 initializerContract "run" State.empty []
  Except.ok (wordEq (state.loadSlot 0) 1))

end SolidCore.Solidity.Witness.PushReturnLength
