import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
FNPTR-STRUCT-MEMBER-CALL (regression): calling through a struct MEMBER that
holds an internal function pointer — `s.fp(x)` where the callee is a
`MemberAccess` on a memory struct value:

```solidity
struct S { uint256 tag; function(uint256) internal pure returns (uint256) fp; }
function dbl(uint256 x) internal pure returns (uint256) { return x * 2; }
function run(uint256 x) external pure returns (uint256) {
    S memory s; s.tag = 7; s.fp = dbl;
    return s.fp(x) + s.tag;
}
```

Gap closed: the member-call typechecker (`s.fp(x)`) never recognised a struct
FIELD of function-pointer type as a callable value — it fell through to
using-function resolution and over-rejected with `unknownFunction "fp"`. The
executable lowering already dispatches an arbitrary-callee internal
function-pointer call via `ptrBoundaryCallExprParts?` (same path as `arr[i](x)`
and `(c ? a : b)(x)`), so once the member-access callee types as an internal
function pointer the call runs.

Real solc 0.8.35 + EVM ground truth for `run(3)`: `dbl(3) + 7 = 6 + 7 = 13`
(0xd), matching the adjudicator's on-chain measurement.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FnPtrStructMemberCall

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [Ty.uint 256] [none] [Ty.uint 256] [none]
    StateMutability.pure Visibility.internal_

private def structS : StructDecl :=
  { name := "S"
    fields :=
      [ { name := "tag", ty := Ty.uint 256 }
      , { name := "fp", ty := fnPtrTy } ] }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.structDecl structS
      -- dbl(x) = x * 2
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "dbl"
          visibility := some Visibility.internal_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [Stmt.returnValues
              (some (Expr.binary BinaryOp.mul (Expr.ident "x")
                (Expr.literal (Literal.number "2"))))]) }
      -- run(x): S memory s; s.tag = 7; s.fp = dbl; return s.fp(x) + s.tag;
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
            [ Stmt.varDecl
                [{ name := some "s", ty := Ty.user { segments := ["S"] },
                   location := some DataLocation.memory }]
                none
            , Stmt.expr
                (Expr.assign
                  (Expr.member (Expr.ident "s") "tag")
                  AssignOp.assign
                  (Expr.literal (Literal.number "7")))
            , Stmt.expr
                (Expr.assign
                  (Expr.member (Expr.ident "s") "fp")
                  AssignOp.assign
                  (Expr.ident "dbl"))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.call
                    (Expr.member (Expr.ident "s") "fp")
                    [Arg.positional (Expr.ident "x")])
                  (Expr.member (Expr.ident "s") "tag"))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- `run(3) = dbl(3) + 7 = 6 + 7 = 13`.
def run_3_is_13 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 13

-- `run(5) = dbl(5) + 7 = 10 + 7 = 17`.
def run_5_is_17 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 5] 17

-- `run(0) = dbl(0) + 7 = 0 + 7 = 7`.
def run_0_is_7 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 0] 7

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_13
#guard isOkTrue run_5_is_17
#guard isOkTrue run_0_is_7

end FnPtrStructMemberCall
end Witness
end Solidity
end SolidCore
