import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
TUPLE-SWAP-STORAGE-PTRS (regression): a tuple assignment that swaps two storage
POINTER locals, then writes through them —

  struct S { uint256 a; }
  S x; S y;
  function run() external returns (uint256) {
    x.a = 1;
    y.a = 2;
    S storage p = x;
    S storage q = y;
    (p, q) = (q, p);   // swap the POINTERS: p -> y, q -> x
    p.a += 100;        // p now y -> y.a = 2 + 100 = 102
    q.a += 200;        // q now x -> x.a = 1 + 200 = 201
    return x.a * 1000 + y.a;
  }

Real solc 0.8.35 + EVM ground truth: the swap re-points the LOCALS (solc stores
the pointer at a `T storage` lvalue — `LValue.cpp` StorageItem repoint — it does
NOT deep-copy through it), so afterwards x.a = 201, y.a = 102 and `run()`
returns 201102.

The bug: the reference-preserving tuple-assignment path only re-pointed MEMORY
pointer locals (`wantsMemoryRefRhs`); a storage-pointer local target instead had
its bare `Expr.var` RHS DEREFERENCED and the LHS resolved to a write-through
storage place. So `(p, q) = (q, p)` swapped the pointed-to CONTENTS (x.a<->y.a
becomes 2/1) while leaving p->x, q->y, giving x.a = 2+100 = 102, y.a = 1+200 =
201 and `run()` = 102201. The fix mirrors the scalar `p = q` re-point
(`Stmt.storageAliasAssignFrom`) inside the tuple write.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleSwapStoragePtrs

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def sTy : Ty := Ty.user ({ segments := ["S"] })
private def member (name field : String) : Expr := Expr.member (Expr.ident name) field
private def storageDecl (name init : String) : Stmt :=
  Stmt.varDecl
    [{ name := some name, ty := sTy, location := some DataLocation.storage }]
    (some (Expr.ident init))

-- (p, q) = (q, p)
private def swap : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.tuple [TupleItem.value (Expr.ident "p"), TupleItem.value (Expr.ident "q")])
    AssignOp.assign
    (Expr.tuple [TupleItem.value (Expr.ident "q"), TupleItem.value (Expr.ident "p")]))

-- x.a * 1000 + y.a
private def retExpr : Expr :=
  Expr.binary BinaryOp.add
    (Expr.binary BinaryOp.mul (member "x" "a") (lit "1000"))
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
            , storageDecl "q" "y"
            , swap
            , Stmt.expr (Expr.assign (member "p" "a") AssignOp.addAssign (lit "100"))
            , Stmt.expr (Expr.assign (member "q" "a") AssignOp.addAssign (lit "200"))
            , Stmt.returnValues (some retExpr) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 201102.
def run_returns_201102 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 201102

-- Final storage: slot 0 (x.a) = 201, slot 1 (y.a) = 102.
def slots_after_swap : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" State.empty []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 201
      && SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 102)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_201102
#guard isOkTrue slots_after_swap

end TupleSwapStoragePtrs
end Witness
end Solidity
end SolidCore
