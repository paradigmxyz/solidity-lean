import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
TUPLE-DECL-TWO-STORAGE-PTRS (regression): a tuple variable DECLARATION that binds
two storage POINTER locals in one statement, then writes through them —

  struct S { uint256 a; }
  S x; S y;
  function run() external returns (uint256) {
    x.a = 1;
    y.a = 2;
    (S storage p, S storage q) = (y, x);  // p -> y, q -> x
    p.a += 10;   // p aliases y -> y.a = 2 + 10 = 12
    q.a += 20;   // q aliases x -> x.a = 1 + 20 = 21
    return x.a * 100 + y.a;               // 21 * 100 + 12 = 2112
  }

Real solc 0.8.35 + EVM ground truth: each declared `S storage` local is bound to
its RHS component's storage LVALUE (a pointer), so the writes THROUGH `p`/`q`
reach the pointed-to state variables. Afterwards x.a = 21, y.a = 12 and `run()`
returns 2112.

The bug: the literal-tuple varDecl lowering declared each storage-pointer local
with a plain `Stmt.varDecl` (a fresh local holding the struct's DEFAULT value)
then ran the flat `assignTuple`. That path's storage-pointer RE-POINT only fires
when the target local ALREADY holds a storage ref — a freshly default-declared
local does not — so the RHS was DEREFERENCED into the local and the through-
writes never reached storage. `run()` returned 102 (x=1, y=2 unchanged) with
storage 0:1;1:2 instead of 2112 with 0:21;1:12. The fix
(`tupleVarDeclAllStorageCore?`) binds each local directly to its component's
storage lvalue, LEFT to RIGHT — identical to the single-binding `S storage p =
y;` lowering.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleDeclTwoStoragePtrs

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def sTy : Ty := Ty.user ({ segments := ["S"] })
private def member (name field : String) : Expr := Expr.member (Expr.ident name) field

-- (S storage p, S storage q) = (y, x)
private def tupleStorageDecl : Stmt :=
  Stmt.varDecl
    [ { name := some "p", ty := sTy, location := some DataLocation.storage }
    , { name := some "q", ty := sTy, location := some DataLocation.storage } ]
    (some (Expr.tuple [TupleItem.value (Expr.ident "y"), TupleItem.value (Expr.ident "x")]))

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
            , tupleStorageDecl
            , Stmt.expr (Expr.assign (member "p" "a") AssignOp.addAssign (lit "10"))
            , Stmt.expr (Expr.assign (member "q" "a") AssignOp.addAssign (lit "20"))
            , Stmt.returnValues (some retExpr) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- Real solc 0.8.35 + EVM ground truth: `run()` returns 2112.
def run_returns_2112 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 2112

-- Final storage: slot 0 (x.a) = 21, slot 1 (y.a) = 12.
def slots_after_decl : Except TypeError Bool := do
  let state ← Examples.checkedOwnCallState 4096 runContract "run" State.empty []
  Except.ok
    (SolidCore.Solidity.Source.wordEq (state.loadSlot 0) 21
      && SolidCore.Solidity.Source.wordEq (state.loadSlot 1) 12)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_returns_2112
#guard isOkTrue slots_after_decl

end TupleDeclTwoStoragePtrs
end Witness
end Solidity
end SolidCore
