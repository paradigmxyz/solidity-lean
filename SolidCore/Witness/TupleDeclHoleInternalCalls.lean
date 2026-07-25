import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
TUPLE-DECL-HOLE-INTERNAL-CALLS (soundness gap): a multi-binding tuple variable
DECLARATION whose RHS is a LITERAL tuple of INTERNAL CALLS and whose LHS has an
anonymous (hole) binding —

  uint256 trace;
  function f() internal returns (uint256) { trace = trace*10+1; return 1; }
  function g() internal returns (uint256) { trace = trace*10+2; return 2; }
  function h(uint256 x) internal returns (uint256) { trace = trace*10+3; return x; }
  function run() public returns (uint256) {
    (uint256 a, , uint256 c) = (f(), g(), h(3));
    return a + c + trace;
  }

Real solc 0.8.35 + EVM ground truth: all three components are evaluated
left-to-right (f: trace 0→1, g: 1→12, h: 12→123), the middle discarded, so
a=1, c=3, trace=123 and run() returns 1+3+123 = 127; storage slot 0 = 123.

The bug: the literal-tuple internal-call declaration arm derives the hoist-temp
types via `VarBindings.sourceTysIncludingAnonymous?`, which FAILS on the anonymous
hole binding (it has no `ty`). The Stage-B fallback then returns `none`, the whole
statement fails to lower, and replay Panics 0 instead of running.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace TupleDeclHoleInternalCalls

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def u256 : Ty := Ty.uint 256
private def lit (s : String) : Expr := Expr.literal (Literal.number s)
private def call0 (fn : String) : Expr := Expr.call (Expr.ident fn) []

-- trace = trace * 10 + k
private def bumpTrace (k : String) : Stmt :=
  Stmt.expr (Expr.assign (Expr.ident "trace") AssignOp.assign
    (Expr.binary BinaryOp.add
      (Expr.binary BinaryOp.mul (Expr.ident "trace") (lit "10")) (lit k)))

private def fFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "f"
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ bumpTrace "1", Stmt.returnValues (some (lit "1")) ]) }

private def gFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "g"
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ bumpTrace "2", Stmt.returnValues (some (lit "2")) ]) }

private def hFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "h"
    visibility := some Visibility.internal_, mutability := StateMutability.nonpayable
    params := [{ name := some "x", ty := u256, location := none }]
    returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block [ bumpTrace "3", Stmt.returnValues (some (Expr.ident "x")) ]) }

-- (uint256 a, , uint256 c) = (f(), g(), h(3)); return a + c + trace;
private def runFn : FunctionDecl :=
  { kind := FunctionKind.function, name := some "run"
    visibility := some Visibility.public_, mutability := StateMutability.nonpayable
    params := [], returns := [{ name := none, ty := u256, location := none }]
    virtual := false, override? := none, modifiers := []
    body := some (Stmt.block
      [ Stmt.varDecl
          [ { name := some "a", ty := some u256, location := none }
          , { name := none, ty := none, location := none }
          , { name := some "c", ty := some u256, location := none } ]
          (some (Expr.tuple
            [ TupleItem.value (call0 "f")
            , TupleItem.value (call0 "g")
            , TupleItem.value (Expr.call (Expr.ident "h") [Arg.positional (lit "3")]) ]))
      , Stmt.returnValues (some (Expr.binary BinaryOp.add
          (Expr.binary BinaryOp.add (Expr.ident "a") (Expr.ident "c"))
          (Expr.ident "trace"))) ]) }

def runContract : ContractDecl :=
{ kind := ContractKind.contract, name := "T", abstract := false, bases := []
  items :=
    [ ContractItem.stateVar
        { name := "trace", ty := u256, visibility := some Visibility.internal_
          mutability := VarMutability.mutable, override? := none, init := none }
    , ContractItem.function fFn
    , ContractItem.function gFn
    , ContractItem.function hFn
    , ContractItem.function runFn ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

def run_is_127 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 4096 runContract "run" State.empty [] 127

private def isOkTrue : Except TypeError Bool → Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_is_127

end TupleDeclHoleInternalCalls
end Witness
end Solidity
end SolidCore
