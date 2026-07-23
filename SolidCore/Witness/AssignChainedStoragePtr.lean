import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
ASSIGN-CHAINED-STORAGE-PTR (regression): a CHAINED storage-pointer assignment
`q = p = y` that re-points BOTH pointers to the same state variable, then writes
THROUGH each —

  struct S { uint256 a; }
  S x; S y;
  function run() external returns (uint256, uint256) {
    x.a = 1;
    y.a = 2;
    S storage p = x;
    S storage q = x;
    q = p = y;            // p -> y, then q -> (p == y)
    p.a = p.a + 10;       // y.a = 2 + 10 = 12
    q.a = q.a + 100;      // y.a = 12 + 100 = 112
    return (x.a, y.a);
  }

Real solc 0.8.35 + EVM ground truth: `p = y` re-points `p` to `y` and its VALUE
is the storage reference now held by `p` (i.e. `y`); the outer `q = (that)`
re-points `q` to `y` as well. Both `p` and `q` alias `y`, so the two writes both
land on `y.a`: 2 -> 12 -> 112. `x.a` is untouched. `run()` returns (1, 112) and
final storage is slot0 (x.a) = 1, slot1 (y.a) = 112.

The bug: the assignment-expression TYPE CHECK discarded the LHS data location
when building the result of `p = y`, so the chained outer `q = p = y` saw a
non-storage RHS and fail-closed with `invalidDataLocation (C.S) storage` — an
over-reject of an in-scope, solc-accepted program. The fix propagates the LHS's
storage-reference location into the assignment-expression result so a chained
pointer rebind is recognized as re-pointing to a storage reference.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace AssignChainedStoragePtr

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def sTy : Ty := Ty.user ({ segments := ["S"] })
private def member (name field : String) : Expr := Expr.member (Expr.ident name) field
private def storageDecl (name init : String) : Stmt :=
  Stmt.varDecl
    [{ name := some name, ty := sTy, location := some DataLocation.storage }]
    (some (Expr.ident init))

-- q = p = y
private def chainedReassign : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.ident "q")
    AssignOp.assign
    (Expr.assign (Expr.ident "p") AssignOp.assign (Expr.ident "y")))

-- p.a = p.a + 10
private def bumpP : Stmt :=
  Stmt.expr (Expr.assign (member "p" "a") AssignOp.assign
    (Expr.binary BinaryOp.add (member "p" "a") (lit "10")))

-- q.a = q.a + 100
private def bumpQ : Stmt :=
  Stmt.expr (Expr.assign (member "q" "a") AssignOp.assign
    (Expr.binary BinaryOp.add (member "q" "a") (lit "100")))

-- return (x.a, y.a)
private def retStmt : Stmt :=
  Stmt.returnValues (some (Expr.tuple
    [TupleItem.value (member "x" "a"), TupleItem.value (member "y" "a")]))

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
          returns :=
            [{ name := none, ty := Ty.uint 256, location := none }
            , { name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.expr (Expr.assign (member "x" "a") AssignOp.assign (lit "1"))
            , Stmt.expr (Expr.assign (member "y" "a") AssignOp.assign (lit "2"))
            , storageDecl "p" "x"
            , storageDecl "q" "x"
            , chainedReassign
            , bumpP
            , bumpQ
            , retStmt ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def emptyState : CoreState := State.empty

-- Real solc 0.8.35 + EVM ground truth: `run()` returns (1, 112).
def run_returns_1_112 : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 4096 runContract "run" emptyState [] 1 112

-- Final storage: slot 0 (x.a) = 1, slot 1 (y.a) = 112.
def slots_after_assign : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" emptyState []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1
      && SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 112)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_1_112
#guard isOkTrue slots_after_assign

end AssignChainedStoragePtr
end Witness
end Solidity
end SolidCore
