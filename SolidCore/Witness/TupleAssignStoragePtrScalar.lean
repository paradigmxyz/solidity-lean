import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
TUPLE-ASSIGN-STORAGE-PTR-SCALAR (regression): a tuple assignment that mixes a
storage POINTER rebind (whose RHS is a bare STATE VARIABLE, not another pointer
local) with a scalar, then writes THROUGH the re-pointed local —

  struct S { uint256 a; }
  S x; S y;
  function run() external returns (uint256) {
    x.a = 1;
    y.a = 2;
    S storage p = x;
    uint256 v;
    (p, v) = (y, uint256(7));  // rebind p -> y, v = 7
    p.a += v;                  // p now y -> y.a = 2 + 7 = 9
    return x.a * 100 + y.a;
  }

Real solc 0.8.35 + EVM ground truth: the tuple assignment re-points the LOCAL `p`
to the state variable `y`'s storage lvalue (solc stores the pointer at a
`T storage` lvalue — it does NOT deep-copy through it). So afterwards x.a = 1,
y.a = 9 and `run()` returns 1*100 + 9 = 109 (storage 0:1; 1:9).

The bug: the reference-preserving tuple-assignment path only re-pointed a
storage-pointer target when its RHS component was another storage-pointer LOCAL
(`lookupStorageBase?`). A bare STATE-VARIABLE RHS (`y`) was DEREFERENCED to a
struct value and the LHS resolved to a write-through storage place, so the
assignment deep-copied y's CONTENTS into x (x.a := 2) while leaving p -> x. Then
`p.a += v` gave x.a = 2 + 7 = 9, y.a = 2, and `run()` returned 9*100 + 2 = 902.
The fix mirrors the scalar `p = y` re-point (`Stmt.storageAliasAssign`) inside
the tuple write for a state-variable RHS.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleAssignStoragePtrScalar

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def sTy : Ty := Ty.user ({ segments := ["S"] })
private def member (name field : String) : Expr := Expr.member (Expr.ident name) field
private def storageDecl (name init : String) : Stmt :=
  Stmt.varDecl
    [{ name := some name, ty := sTy, location := some DataLocation.storage }]
    (some (Expr.ident init))

-- uint256 v;
private def vDecl : Stmt :=
  Stmt.varDecl
    [{ name := some "v", ty := Ty.uint 256, location := none }]
    none

-- (p, v) = (y, uint256(7))
private def tupleAssign : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.tuple [TupleItem.value (Expr.ident "p"), TupleItem.value (Expr.ident "v")])
    AssignOp.assign
    (Expr.tuple [TupleItem.value (Expr.ident "y"), TupleItem.value (lit "7")]))

-- x.a * 100 + y.a
private def retExpr : Expr :=
  Expr.binary BinaryOp.add
    (Expr.binary BinaryOp.mul (member "x" "a") (lit "100"))
    (member "y" "a")

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.structDecl
        { name := "S", fields := [{ name := "a", ty := Ty.uint 256 }] }
    , ContractItem.stateVar
        { name := "x", ty := sTy, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.stateVar
        { name := "y", ty := sTy, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
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
            [ Stmt.expr (Expr.assign (member "x" "a") AssignOp.assign (lit "1"))
            , Stmt.expr (Expr.assign (member "y" "a") AssignOp.assign (lit "2"))
            , storageDecl "p" "x"
            , vDecl
            , tupleAssign
            , Stmt.expr (Expr.assign (member "p" "a") AssignOp.addAssign (Expr.ident "v"))
            , Stmt.returnValues (some retExpr) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 109.
def run_returns_109 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 109

-- Final storage: slot 0 (x.a) = 1, slot 1 (y.a) = 9.
def slots_after_assign : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" State.empty []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1
      && SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 9)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_109
#guard isOkTrue slots_after_assign

end TupleAssignStoragePtrScalar
end Witness
end Solidity
end SolidCore
