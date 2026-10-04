import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
Tuple assignment computes both side-effecting storage indexes after evaluating
the RHS. The index expressions contain calls inside `%`, not direct calls.
With `cursor` initially zero, `tick(1)` returns 2 and `tick(2)` returns 261;
the stores land at indexes 2 and 5, and `cursor` ends at 259.
-/

namespace SolidCore.Solidity.Witness.TupleAssignComputedIndexCalls

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (n : String) : Expr := Expr.literal (Literal.number n)
private def u256 : Ty := Ty.uint 256
private def binary (op : BinaryOp) (a b : Expr) : Expr := Expr.binary op a b
private def tickCall (n : String) : Expr :=
  Expr.call (Expr.ident "tick") [Arg.positional (lit n)]
private def index (n : String) : Expr :=
  Expr.index (Expr.ident "values")
    (binary BinaryOp.mod (tickCall n) (lit "8"))

private def tickFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "tick"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    params := [{ name := some "input", ty := u256 }]
    returns := [{ name := none, ty := u256 }]
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign (Expr.ident "cursor") AssignOp.assign
          (binary BinaryOp.add
            (binary BinaryOp.mul (Expr.ident "cursor") (lit "257"))
            (Expr.ident "input")))
      , Stmt.returnValues
          (some (binary BinaryOp.add (Expr.ident "input")
            (Expr.ident "cursor"))) ]) }

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    returns := [{ name := none, ty := u256 }]
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign
          (Expr.tuple [TupleItem.value (index "1"),
            TupleItem.value (index "2")]) AssignOp.assign
          (Expr.tuple [TupleItem.value (lit "11"),
            TupleItem.value (lit "13")]))
      , Stmt.returnValues
          (some (Expr.index (Expr.ident "values") (lit "0"))) ]) }

def contract : ContractDecl :=
  { kind := ContractKind.contract
    name := "C"
    items :=
      [ ContractItem.stateVar { name := "values", ty := Ty.array u256 (some 8) }
      , ContractItem.stateVar { name := "cursor", ty := u256 }
      , ContractItem.function tickFn
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

def returnMatches : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 contract "run" State.empty [] 0

def storageMatches : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 contract "run" State.empty []
  Except.ok
    (wordEq (state.loadSlot 2) 11 &&
      wordEq (state.loadSlot 5) 13 &&
      wordEq (state.loadSlot 8) 259)

#guard accepted
#guard isOkTrue returnMatches
#guard isOkTrue storageMatches

end SolidCore.Solidity.Witness.TupleAssignComputedIndexCalls
