import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A direct write to a wide signed array element masks to the source width,
whereas a whole-array copy of a negative element stores its sign-extended
word. Both paths occupy one slot per element.
-/

namespace SolidCore.Solidity.Witness.WideSignedArrayElementWrite

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def num (s : String) : Expr := Expr.literal (Literal.number s)
private def neg (s : String) : Expr := Expr.unary UnaryOp.neg (num s)
private def element : Expr := Expr.index (Expr.ident "values") (num "0")

private def runFn (name : String) (rhs : Expr) (whole : Bool) : FunctionDecl :=
  { kind := FunctionKind.function
    name := some name
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.int 192 }]
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign
          (if whole then Expr.ident "values" else element)
          AssignOp.assign rhs)
      , Stmt.returnValues (some element) ]) }

private def deleteWholeFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "deleteWhole"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := Ty.int 192 }]
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign (Expr.ident "values") AssignOp.assign
          (Expr.array [Expr.call (Expr.typeName (Ty.int 192))
            [Arg.positional (neg "2")]]))
      , Stmt.expr (Expr.unary UnaryOp.delete (Expr.ident "values"))
      , Stmt.returnValues (some element) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar
          { name := "values", ty := Ty.array (Ty.int 192) (some 1) }
      , ContractItem.function (runFn "direct" (neg "1") false)
      , ContractItem.function
          (runFn "copy" (Expr.array
            [Expr.call (Expr.typeName (Ty.int 192))
              [Arg.positional (neg "2")]]) true)
      , ContractItem.function deleteWholeFn ] }

def sourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "0.8.35",
              SourceItem.contract contract] }

def accepted : Bool :=
  TypeCheck.Result.isOk
    (TypeCheck.TypecheckedInput.checkedSourceUnit sourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

def directMasks : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "direct" State.empty []
  Except.ok (wordEq (state.loadSlot 0) (2 ^ 192 - 1))

def copySignExtends : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "copy" State.empty []
  Except.ok (wordEq (state.loadSlot 0)
    (SolidCore.Solidity.Shared.signedToWord (-2)))

def wholeDeleteClears : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "deleteWhole" State.empty []
  Except.ok (wordEq (state.loadSlot 0) 0)

#guard accepted
#guard isOkTrue directMasks
#guard isOkTrue copySignExtends
#guard isOkTrue wholeDeleteClears

end SolidCore.Solidity.Witness.WideSignedArrayElementWrite
