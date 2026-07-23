import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
TUPLE-ASSIGN-INDEX-CALL-ORDER (regression): a tuple ASSIGNMENT whose LHS index
expressions are INTERNAL CALLS and whose RHS is a multi-return internal call —

  uint256[16] public arr;
  mapping(uint256 => uint256) public m;
  uint256 public n;
  function bump() internal returns (uint256) { n += 1; return n; }
  function two() internal returns (uint256, uint256) { n += 10; return (n*100, n*100+1); }
  function run() external returns (uint256, uint256, uint256) {
    (m[bump()], arr[bump()]) = two();
    ...
  }

Real solc 0.8.35 + EVM ground truth: the RHS is evaluated BEFORE the LHS index
expressions. So `two()` runs first (n: 0 -> 10, returns (1000, 1001)), THEN the
LHS indices left-to-right: `bump()` -> n=11 (m key 11), `bump()` -> n=12 (arr
index 12). Final: m[11]=1000, arr[12]=1001, n=12. run() returns
(mSum, aSum, n) = (13000, 17017, 12).

The bug: the importer hoisted the LHS index calls BEFORE the RHS call, so the
model evaluated `bump()`,`bump()` first (n=1, n=2) then `two()` (n=12), writing
m[1]=1200, arr[2]=1201 and returning (1200, 8407, 12).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleAssignIndexCallOrder

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def u256 : Ty := Ty.uint 256
private def call0 (fn : String) : Expr := Expr.call (Expr.ident fn) []

-- n*100
private def nTimes100 : Expr :=
  Expr.binary BinaryOp.mul (Expr.ident "n") (lit "100")

-- bump(): n += 1; return n;
private def bumpFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "bump"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    params := []
    returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (lit "1"))
      , Stmt.returnValues (some (Expr.ident "n")) ]) }

-- two(): n += 10; return (n*100, n*100+1);
private def twoFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "two"
    visibility := some Visibility.internal_
    mutability := StateMutability.nonpayable
    params := []
    returns :=
      [ { name := none, ty := u256, location := none }
      , { name := none, ty := u256, location := none } ]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.expr (Expr.assign (Expr.ident "n") AssignOp.addAssign (lit "10"))
      , Stmt.returnValues (some (Expr.tuple
          [ TupleItem.value nTimes100
          , TupleItem.value (Expr.binary BinaryOp.add nTimes100 (lit "1")) ])) ]) }

-- (m[bump()], arr[bump()]) = two();
private def tupleAssignStmt : Stmt :=
  Stmt.expr (Expr.assign
    (Expr.tuple
      [ TupleItem.value (Expr.index (Expr.ident "m") (call0 "bump"))
      , TupleItem.value (Expr.index (Expr.ident "arr") (call0 "bump")) ])
    AssignOp.assign
    (call0 "two"))

-- m[1] + m[2]*7 + m[11]*13 + m[12]*17   (and arr version)
private def weighted (base : String) : Expr :=
  let term (k w : String) : Expr :=
    Expr.binary BinaryOp.mul (Expr.index (Expr.ident base) (lit k)) (lit w)
  Expr.binary BinaryOp.add
    (Expr.binary BinaryOp.add
      (Expr.binary BinaryOp.add (Expr.index (Expr.ident base) (lit "1")) (term "2" "7"))
      (term "11" "13"))
    (term "12" "17")

private def runFn : FunctionDecl :=
  { kind := FunctionKind.function
    name := some "run"
    visibility := some Visibility.external_
    mutability := StateMutability.nonpayable
    params := []
    returns :=
      [ { name := none, ty := u256, location := none }
      , { name := none, ty := u256, location := none }
      , { name := none, ty := u256, location := none } ]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ tupleAssignStmt
      , Stmt.varDecl [{ name := some "mSum", ty := u256, location := none }]
          (some (weighted "m"))
      , Stmt.varDecl [{ name := some "aSum", ty := u256, location := none }]
          (some (weighted "arr"))
      , Stmt.returnValues (some (Expr.tuple
          [ TupleItem.value (Expr.ident "mSum")
          , TupleItem.value (Expr.ident "aSum")
          , TupleItem.value (Expr.ident "n") ])) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.stateVar
        { name := "arr", ty := Ty.array u256 (some 16)
          visibility := some Visibility.public_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.stateVar
        { name := "m", ty := Ty.mapping u256 u256
          visibility := some Visibility.public_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.stateVar
        { name := "n", ty := u256
          visibility := some Visibility.public_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function bumpFn
    , ContractItem.function twoFn
    , ContractItem.function runFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

private def wordsMatch :
    List SolidCore.Solidity.Source.Value -> List Word -> Bool
  | [], [] => true
  | SolidCore.Solidity.Source.Value.word value :: values, expected :: rest =>
      SolidCore.Solidity.Source.wordEq value expected && wordsMatch values rest
  | _, _ => false

def returned (expected : List Word) : Except TypeError Bool := do
  let result ←
    CheckedInput.ownCall 4096 runContract
      (SolidCore.Solidity.Source.CallTarget.name "run")
      SolidCore.Solidity.Source.State.empty []
  match result with
  | SolidCore.Solidity.Source.CallResult.returned _ values =>
      Except.ok (wordsMatch values expected)
  | _ => Except.ok false

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- EVM ground truth: RHS-before-LHS-index → run() returns (13000, 17017, 12).
def run_matches_evm : Except TypeError Bool := returned [13000, 17017, 12]

#guard accepted
#guard isOkTrue run_matches_evm

end TupleAssignIndexCallOrder
end Witness
end Solidity
end SolidCore
