import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
ASSIGN-TERNARY-STORAGE-PTR (regression): re-pointing an EXISTING storage POINTER
from a conditional that selects between two bare STATE VARIABLES, then writing
THROUGH the re-pointed local —

  struct S { uint256 a; }
  S x; S y;
  bool flag = true;
  function run() external returns (uint256, uint256) {
    x.a = 1;
    y.a = 2;
    S storage p = x;
    p = flag ? y : x;   // flag == true, so re-point p -> y
    p.a = 55;           // p now aliases y -> y.a = 55
    return (x.a, y.a);
  }

Real solc 0.8.35 + EVM ground truth: the ternary is itself a storage-reference
lvalue; assigning it to the pointer `p` RE-POINTS `p` to the SELECTED branch (`y`,
since `flag` is true). It does NOT deep-copy through the original alias. So the
later `p.a = 55` writes `y.a`, leaving x.a = 1, y.a = 55, and `run()` returns
(1, 55) (storage 0:1; 1:55).

The bug: the alias-ASSIGN lowering (`storageAliasAssignmentExprCore?`) only
handled bare-ident and index/member-path RHS shapes; a TERNARY RHS returned none
and fell through to generic assignment lowering, which left `p` aliasing its
original decl target `x`. So `p.a = 55` wrote x.a = 55 and `run()` returned
(55, 2) (storage 0:55; 1:2). The fix branches a ternary RHS into an `ifElse` that
runs the matching re-point ASSIGN in the current scope, mirroring the existing
decl-from-ternary form (`storageAliasDeclFromTernaryCore?`).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace AssignTernaryStoragePtr

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def sTy : Ty := Ty.user ({ segments := ["S"] })
private def member (name field : String) : Expr := Expr.member (Expr.ident name) field
private def storageDecl (name init : String) : Stmt :=
  Stmt.varDecl
    [{ name := some name, ty := sTy, location := some DataLocation.storage }]
    (some (Expr.ident init))

-- p = flag ? y : x
private def ptrReassign : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.ident "p")
    AssignOp.assign
    (Expr.ternary (Expr.ident "flag") (Expr.ident "y") (Expr.ident "x")))

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
    , ContractItem.stateVar
        { name := "flag", ty := Ty.bool, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none
          init := some (Expr.literal (Literal.bool true)) }
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
            , ptrReassign
            , Stmt.expr (Expr.assign (member "p" "a") AssignOp.assign (lit "55"))
            , retStmt ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Deployed state: `bool flag = true` is set by the constructor at construction,
-- i.e. storage slot 2 = 1. `checkedOwnCall` invokes `run` directly (no
-- constructor), so seed the slot to match the on-chain deployed contract.
def deployedState : CoreState := State.empty.storeSlot 2 1

-- Real solc 0.8.35 + EVM ground truth: `run()` returns (1, 55).
def run_returns_1_55 : Except TypeError Bool :=
  Examples.checkedOwnCallWordPairMatches 4096 runContract "run" deployedState [] 1 55

-- Final storage: slot 0 (x.a) = 1, slot 1 (y.a) = 55.
def slots_after_assign : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" deployedState []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 1
      && SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 55)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_1_55
#guard isOkTrue slots_after_assign

end AssignTernaryStoragePtr
end Witness
end Solidity
end SolidCore
