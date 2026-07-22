import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
FNPTR-RETURNED-THEN-CALL (regression): an internal function returns an internal
function pointer which is IMMEDIATELY called — `pick(true)(x)`. The outer
`FunctionCall`'s callee is itself a `FunctionCall` (`Expr.call (Expr.call …) …`),
the same non-identifier internal function-pointer callee boundary as `arr[i](x)`
in [[internal-call-name-keying]], `(c ? a : b)(x)`, and `s.fp(x)`:

```solidity
function dbl(uint256 x) internal pure returns (uint256) { return x * 2; }
function trp(uint256 x) internal pure returns (uint256) { return x * 3; }
function pick(bool c) internal pure
    returns (function(uint256) internal pure returns (uint256)) {
    if (c) { return dbl; }
    return trp;
}
function run(uint256 x) external pure returns (uint256) {
    return pick(true)(x) + pick(false)(x);
}
```

Gap closed: the solc-AST importer left `FunctionCall.argumentTypes.typeIdentifier`
/ `.typeString` UNCLASSIFIED. solc annotates the callee expression of a call with
`argumentTypes` (the call's argument types) for every callee node shape —
`Identifier`, `MemberAccess`, `IndexAccess`, `TupleExpression`, … — but the
`FunctionCall` callee case (a returned function pointer that is directly called)
was omitted, so an in-scope, solc-accepted program failed closed at import. The
executable lowering already routes an arbitrary-callee internal
function-pointer call via `ptrBoundaryCallExprParts?` (`Expr.call callee args`
arm), so once the importer stops fail-closing the call runs.

Real solc 0.8.35 + EVM ground truth for `run(3)`:
  `pick(true)(3) = dbl(3) = 6`, `pick(false)(3) = trp(3) = 9`, `6 + 9 = 15`
(0xf), matching the adjudicator's on-chain measurement.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FnPtrReturnedThenCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [Ty.uint 256] [none] [Ty.uint 256] [none]
    StateMutability.pure Visibility.internal_

private def unaryFn (name : Name) (body : Stmt) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function
      name := some name
      visibility := some Visibility.internal_
      mutability := StateMutability.pure
      params := [{ name := some "x", ty := Ty.uint 256, location := none }]
      returns := [{ name := none, ty := Ty.uint 256, location := none }]
      virtual := false
      override? := none
      modifiers := []
      body := some body }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ -- dbl(x) = x * 2
      unaryFn "dbl"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.mul (Expr.ident "x")
              (Expr.literal (Literal.number "2"))))])
      -- trp(x) = x * 3
    , unaryFn "trp"
        (Stmt.block
          [Stmt.returnValues
            (some (Expr.binary BinaryOp.mul (Expr.ident "x")
              (Expr.literal (Literal.number "3"))))])
      -- pick(c): if (c) return dbl; return trp;
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "pick"
          visibility := some Visibility.internal_
          mutability := StateMutability.pure
          params := [{ name := some "c", ty := Ty.bool, location := none }]
          returns := [{ name := none, ty := fnPtrTy, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [ Stmt.ifElse (Expr.ident "c")
                (Stmt.block [Stmt.returnValues (some (Expr.ident "dbl"))]) none
            , Stmt.returnValues (some (Expr.ident "trp")) ]) }
      -- run(x): return pick(true)(x) + pick(false)(x);
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "run"
          visibility := some Visibility.external_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [Stmt.returnValues
              (some (Expr.binary BinaryOp.add
                (Expr.call
                  (Expr.call (Expr.ident "pick")
                    [Arg.positional (Expr.literal (Literal.bool true))])
                  [Arg.positional (Expr.ident "x")])
                (Expr.call
                  (Expr.call (Expr.ident "pick")
                    [Arg.positional (Expr.literal (Literal.bool false))])
                  [Arg.positional (Expr.ident "x")])))]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- `run(3) = dbl(3) + trp(3) = 6 + 9 = 15`.
def run_3_is_15 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 15

-- `run(5) = dbl(5) + trp(5) = 10 + 15 = 25`.
def run_5_is_25 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 5] 25

-- `run(0) = dbl(0) + trp(0) = 0 + 0 = 0`.
def run_0_is_0 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 0] 0

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_15
#guard isOkTrue run_5_is_25
#guard isOkTrue run_0_is_0

end FnPtrReturnedThenCall
end Witness
end Solidity
end SolidCore
