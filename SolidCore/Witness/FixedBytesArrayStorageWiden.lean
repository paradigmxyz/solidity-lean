import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
A memory-to-storage array copy must apply the element conversion, including the
right-padding rule for fixed bytes. In the internal right-aligned bytesN
representation, widening bytes4("cdef") to bytes10 shifts the payload left by
six bytes before the storage lane is written.
-/

open SolidCore.Solidity
open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

namespace SolidCore.Solidity.Witness.FixedBytesArrayStorageWiden

private def num (s : String) : Expr := Expr.literal (Literal.number s)

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    params := []
    returns := [{ name := none, ty := Ty.bytesN 10, location := none }]
    virtual := false
    override? := none
    modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [{ name := some "m", ty := some (Ty.array (Ty.bytesN 4) none),
             location := some DataLocation.memory }]
          (some (Expr.newExpr (Ty.array (Ty.bytesN 4) none)
            [Arg.positional (num "3")]))
      , Stmt.expr
          (Expr.assign
            (Expr.index (Expr.ident "m") (num "2"))
            AssignOp.assign (Expr.literal (Literal.string "cdef")))
      , Stmt.expr
          (Expr.assign (Expr.ident "s") AssignOp.assign (Expr.ident "m"))
      , Stmt.returnValues
          (some (Expr.index (Expr.ident "s") (num "2"))) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    abstract := false
    bases := []
    items :=
      [ ContractItem.stateVar
          { name := "s"
            ty := Ty.array (Ty.bytesN 10) none
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

def copiedValue : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 512 contract "run" State.empty []
    0x636465660000000000000000

def copiedStorageLane : Except TypeError Bool := do
  let state ←
    Examples.checkedOwnCallState 512 contract "run" State.empty []
  Except.ok
    (wordEq
      (state.loadSlot
        18569430475105882587588266137607568536673111973893317399460219858819262702947)
      0x636465660000000000000000000000000000000000000000000000000000)

#guard accepted
#guard isOkTrue copiedValue
#guard isOkTrue copiedStorageLane

end SolidCore.Solidity.Witness.FixedBytesArrayStorageWiden
