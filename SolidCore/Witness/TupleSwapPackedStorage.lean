import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
TUPLE-SWAP-PACKED-STORAGE (regression): a tuple assignment that swaps two
PACKED scalar state variables sharing one storage slot —

  uint256[] a;
  uint64 x = 3;
  uint64 y = 4;
  function run() external returns (uint256) {
    a.push(1); a.push(2);
    (a[0], a[1]) = (a[1], a[0]);   // separate slots — already correct
    (x, y) = (y, x);               // packed in slot 1 — used to break
    return a[0]*10000 + a[1]*1000 + uint256(x)*100 + uint256(y);
  }

Real solc 0.8.35 + EVM: the swap leaves x=4, y=3, so `run()` returns 21403 and
slot 1 = x + (y<<64) = 4 + (3<<64) = 55340232221128654852.

The bug: the reference-preserving tuple-assignment RHS lowers a bare packed
state-variable read to `Expr.storagePath name []`, whose reader
(`resolveStorageBasePath` → `storageBaseAnchor`) drove off the field's
whole-word `scalar` layout and ignored the packed sub-slot offset/width kept on
the `StorageField` record. Both `x` and `y` therefore read back the WHOLE slot
(3 + 4<<64); coerced back to `uint64` on store both truncated to 3, giving
x=3, y=3 → `run()` returned 21303 and slot 1 = 55340232221128654851.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleSwapPackedStorage

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def u256 (e : Expr) : Expr :=
  Expr.call (Expr.typeName (Ty.uint 256)) [Arg.positional e]
private def idx (name : String) (i : String) : Expr :=
  Expr.index (Expr.ident name) (lit i)
private def push (name : String) (v : String) : Stmt :=
  Stmt.expr (Expr.call (Expr.member (Expr.ident name) "push") [Arg.positional (lit v)])
private def tupleAssign (lhs rhs : List Expr) : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.tuple (lhs.map TupleItem.value))
    AssignOp.assign
    (Expr.tuple (rhs.map TupleItem.value)))

-- a[0]*10000 + a[1]*1000 + uint256(x)*100 + uint256(y)
private def retExpr : Expr :=
  Expr.binary BinaryOp.add
    (Expr.binary BinaryOp.add
      (Expr.binary BinaryOp.add
        (Expr.binary BinaryOp.mul (idx "a" "0") (lit "10000"))
        (Expr.binary BinaryOp.mul (idx "a" "1") (lit "1000")))
      (Expr.binary BinaryOp.mul (u256 (Expr.ident "x")) (lit "100")))
    (u256 (Expr.ident "y"))

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "a"
          ty := Ty.array (Ty.uint 256) none
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := none }
    , ContractItem.stateVar
        { name := "x"
          ty := Ty.uint 64
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := some (lit "3") }
    , ContractItem.stateVar
        { name := "y"
          ty := Ty.uint 64
          visibility := some Visibility.internal_
          mutability := VarMutability.mutable
          override? := none
          init := some (lit "4") }
    , ContractItem.function
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
            [ push "a" "1"
            , push "a" "2"
            , tupleAssign [idx "a" "0", idx "a" "1"] [idx "a" "1", idx "a" "0"]
            , tupleAssign [Expr.ident "x", Expr.ident "y"]
                          [Expr.ident "y", Expr.ident "x"]
            , Stmt.returnValues (some retExpr) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Deploy the contract so the field initializers `uint64 x = 3; uint64 y = 4;`
-- run (packed slot 1 = 3 + (4<<64) = 73786976294838206467), matching the
-- post-deploy state the adjudicator's call observes.
def deployedState : Except TypeError CoreState := do
  let result ← CheckedInput.ownConstruct 4096 runContract State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned state _ => Except.ok state
  | _ => Except.error (executableFailure "constructor")

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 21403.
def run_returns_21403 : Except TypeError Bool := do
  let state ← deployedState
  Examples.checkedOwnCallWordMatches 4096 runContract "run" state [] 21403

-- Final storage: slot 1 (packed x,y) = 4 + (3<<64) = 55340232221128654852.
def slot1_packed_after_swap : Except TypeError Bool := do
  let state ← deployedState
  let state ← Examples.checkedOwnCallState 4096 runContract "run" state []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 55340232221128654852)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_21403
#guard isOkTrue slot1_packed_after_swap

end TupleSwapPackedStorage
end Witness
end Solidity
end SolidCore
