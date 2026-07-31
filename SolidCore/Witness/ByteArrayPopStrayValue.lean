import SolidCore.Solidity.Checked
import SolidCore.Witness.Checked

set_option maxHeartbeats 8000000

/-!
BYTE-ARRAY-POP-STRAY-VALUE (C, over_reject) — a bare reference to the builtin
storage-array `pop` mutation member used as a discarded expression statement.

```solidity
contract c {
    bytes data;
    function test() public returns (uint256 x) {
        data.pop;
    }
}
```

`data.pop;` names the builtin storage `bytes`/dynamic-array `pop` mutation member
as a VALUE and immediately discards it (an expression statement). solc 0.8.35 +
EVM ACCEPT this (with a "statement has no effect" warning): the member access
yields the mutation function's type, but nothing CALLS it, so the pop never runs
— storage is UNCHANGED — and `test` runs to the end returning its default
`x == 0` (measured EVM return `0x00…00`). Naming `push`/`pop` as a bare,
discarded reference is legal; only a genuine CALL (`data.pop()`) mutates.

solidity-lean over-rejected (fail-closed): `checkExpr`'s `Expr.member base member`
arm has no VALUE form for an uncalled `push`/`pop` (they are call-only mutation
members, resolved only in `checkArrayMutationCall?` at a CALL site), so the bare
reference fell to `unsupported "member pop"`.

Fix (mirrors the LIBRARY, ABI and UDVT STRAY-VALUE arcs, #69/#70/#71): accept
`data.push;` / `data.pop;` as a discarded no-op STATEMENT at the typecheck gate
(statement position only, over a plain identifier base that is genuinely a
storage dynamic array / `bytes` — the same success condition as the storage
push/pop CALL path) and drop the effect-free statement in the executable lowering
(`Expr.isStrayLibraryFunctionValue` now also matches a bare `x.push`/`x.pop`
member value, elided by `Stmt.dropStrayLibraryFunctionValues`). A `push`/`pop`
member in a CONVERSION position, on a fixed-size array, or on a memory/calldata
receiver stays rejected — `checkExpr` is unchanged.
-/

namespace SolidCore
namespace Solidity
namespace Witness
namespace ByteArrayPopStrayValue

open SolidCore.Solidity.Source
open SolidCore.Solidity.TypeCheck

-- bytes data;
private def dataVar : ContractItem :=
  ContractItem.stateVar { name := "data", ty := Ty.bytes }

-- function test() public returns (uint256 x) { data.pop; }
private def testFn (member : Name) : ContractItem :=
  ContractItem.function
    { kind := FunctionKind.function, name := some "test"
      visibility := some Visibility.public_, mutability := StateMutability.nonpayable
      params := []
      returns := [{ name := some "x", ty := Ty.uint 256, location := none }]
      virtual := false, override? := none, modifiers := []
      body := some (Stmt.block
        [Stmt.expr (Expr.member (Expr.ident "data") member)]) }

private def mkContract (member : Name) : ContractDecl :=
  { kind := ContractKind.contract, name := "c", abstract := false, bases := []
    items := [dataVar, testFn member] }

private def mkSU (member : Name) : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
              SourceItem.contract (mkContract member)] }

def sourceUnit : SourceUnit := mkSU "pop"
def pushSourceUnit : SourceUnit := mkSU "push"

-- Typechecks (was fail-closed over_reject `unsupported "member pop"`).
def accepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit sourceUnit)
def pushAccepted : Bool :=
  TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit pushSourceUnit)

private def isOkTrue : Except TypeError Bool -> Bool
  | Except.ok true => true
  | _ => false

-- `test()`: the stray `data.pop;` is a discarded no-op; `test` runs to the end
-- returning its default `x == 0` (matching solc+EVM `0x00…00`), NOT a
-- fail-closed reject and NOT a Panic.
private def returnsZeroFor (su : SourceUnit) : Except TypeError Bool := do
  let result ←
    CheckedInput.callContract 4096 su "c"
      (CallTarget.name "test") State.empty []
  match result with
  | CallResult.returned _ [Value.word v] => Except.ok (wordEq v 0)
  | CallResult.returned _ [Value.int v] => Except.ok (wordEq v 0)
  | _ => Except.ok false

def test_returns_zero : Except TypeError Bool := returnsZeroFor sourceUnit
def push_returns_zero : Except TypeError Bool := returnsZeroFor pushSourceUnit

-- ---------------------------------------------------------------------------
-- Control: the gate is TIGHT. A bare `pop` on a FIXED-size storage array has no
-- builtin `push`/`pop`, so the stray-value acceptance must NOT fire — it stays a
-- fail-closed reject, exactly like solc.
-- ---------------------------------------------------------------------------
private def fixedSU : SourceUnit :=
  { items := [SourceItem.pragma "solidity" "^0.8.35",
      SourceItem.contract
      { kind := ContractKind.contract, name := "c", abstract := false, bases := []
        items :=
          [ ContractItem.stateVar { name := "fa", ty := Ty.array (Ty.uint 256) (some 3) }
          , ContractItem.function
              { kind := FunctionKind.function, name := some "test"
                visibility := some Visibility.public_
                mutability := StateMutability.nonpayable
                returns := [{ name := some "x", ty := Ty.uint 256, location := none }]
                body := some (Stmt.block
                  [Stmt.expr (Expr.member (Expr.ident "fa") "pop")]) } ] }] }

def fixedRejected : Bool :=
  !(TypeCheck.Result.isOk (TypecheckedInput.checkedSourceUnit fixedSU))

#guard accepted
#guard pushAccepted
#guard isOkTrue test_returns_zero
#guard isOkTrue push_returns_zero
#guard fixedRejected

end ByteArrayPopStrayValue
end Witness
end Solidity
end SolidCore
