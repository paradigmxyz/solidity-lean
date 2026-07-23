import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 12000000

/-!
FNPTR-STRUCT-CONSTRUCTOR-MEMBER-VALUE (regression): a struct built with the
POSITIONAL constructor `S(f, …)` whose FIELD is an internal function pointer,
then read BY VALUE into a local and called via the local identifier:

```solidity
struct S { function(uint256) internal pure returns (uint256) fp; uint256 tag; }
function a(uint256 x) internal pure returns (uint256) { return x + 5; }
function run(uint256 x) external pure returns (uint256) {
    S memory s = S(a, 9);
    function(uint256) internal pure returns (uint256) f = s.fp;
    return f(x) + s.tag;
}
```

Gap closed: `resolveStructs` lowers `S(a, 9)` to a tuple whose fn-pointer FIELD
is `function(...)(<dispatch-id>)` — a conversion of the (fn-value rewritten)
dispatch-ID number literal to the field's internal-function type. The struct/
tuple element lowering runs through the TARGET-LESS `Expr.toCore?`, whose
generic `typeName`-conversion arm treated the number literal as a numeric cast
and produced a bare `Expr.word <id>` instead of an `Expr.internalFunction <id>`
pointer value. The stored field was then a plain word, so reading it into `f`
and calling `f(x)` hit the internal-function-pointer call's type-mismatch
fall-through and Panicked 0 — where solc dispatches and returns. `Expr.toCore?`
now consults `Expr.toCoreInternalFunctionValueLiteralAs?` in that arm (the same
value-production the target-aware `toCoreAs?` and env-aware `toCoreAsWithEnv?`
already use), so the field carries the dispatch-ID pointer value.

Real solc 0.8.35 + EVM ground truth for `run(3)`: `a(3) + 9 = 8 + 9 = 17`,
matching the adjudicator's on-chain measurement (0x11).
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace FnPtrStructConstructorMemberValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

private def fnPtrTy : Ty :=
  Ty.functionWithLocations [Ty.uint 256] [none] [Ty.uint 256] [none]
    StateMutability.pure Visibility.internal_

private def structS : StructDecl :=
  { name := "S"
    fields :=
      [ { name := "fp", ty := fnPtrTy }
      , { name := "tag", ty := Ty.uint 256 } ] }

def runContract : ContractDecl :=
{ kind := ContractKind.contract
  name := "C"
  abstract := false
  bases := []
  items :=
    [ ContractItem.structDecl structS
      -- a(x) = x + 5
    , ContractItem.function
        { kind := FunctionKind.function
          name := some "a"
          visibility := some Visibility.internal_
          mutability := StateMutability.pure
          params := [{ name := some "x", ty := Ty.uint 256, location := none }]
          returns := [{ name := none, ty := Ty.uint 256, location := none }]
          virtual := false
          override? := none
          modifiers := []
          body := some (Stmt.block
            [Stmt.returnValues
              (some (Expr.binary BinaryOp.add (Expr.ident "x")
                (Expr.literal (Literal.number "5"))))]) }
      -- run(x): S memory s = S(a, 9); f = s.fp; return f(x) + s.tag;
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
                (some (Expr.call (Expr.typeName (Ty.user { segments := ["S"] }))
                  [ Arg.positional (Expr.ident "a")
                  , Arg.positional (Expr.literal (Literal.number "9")) ]))
            , Stmt.varDecl
                [{ name := some "f", ty := fnPtrTy, location := none }]
                (some (Expr.member (Expr.ident "s") "fp"))
            , Stmt.returnValues
                (some (Expr.binary BinaryOp.add
                  (Expr.call (Expr.ident "f") [Arg.positional (Expr.ident "x")])
                  (Expr.member (Expr.ident "s") "tag"))) ]) } ] }

def runSourceUnit : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35", SourceItem.contract runContract] }

def accepted : Bool :=
  TypeCheck.Result.isOk (TypeCheck.TypecheckedInput.checkedSourceUnit runSourceUnit)

-- `run(3) = a(3) + 9 = 8 + 9 = 17`.
def run_3_is_17 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 3] 17

-- `run(0) = a(0) + 9 = 5 + 9 = 14`.
def run_0_is_14 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 0] 14

-- `run(10) = a(10) + 9 = 15 + 9 = 24`.
def run_10_is_24 : Except TypeError Bool :=
  Examples.checkedOwnCallWordMatches 256 runContract "run" State.empty
    [Value.word 10] 24

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

#guard accepted
#guard isOkTrue run_3_is_17
#guard isOkTrue run_0_is_14
#guard isOkTrue run_10_is_24

end FnPtrStructConstructorMemberValue
end Witness
end Solidity
end SolidCore
