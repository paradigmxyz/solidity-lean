# solc function-types / selectors / function-pointers review

Search-only divergence hunt on the function-type surface (selectors, external
function values, internal function pointers, mutability covariance) vs pinned
solc 0.8.35 (legacy codegen: optimizer=false, no via_ir). Ground truth gathered
with Forge 1.5.1 + pinned solc; solidity-lean behaviour read from
`SolidCore/Solidity/{Interpreter,Interface,TypeCheck,ABI}.lean` and confirmed
with direct `lake env lean` `#eval`s on the interpreter.

## DIVERGENCE 1 — internal function-pointer equality reverts instead of returning bool  (confidence 92%, severity: wrong-value / spurious-revert)

**Program**
```solidity
contract C {
  function g(uint x) internal pure returns (uint) { return x; }
  function h(uint x) internal pure returns (uint) { return x; }
  function eqSame() external pure returns (bool) {
    function(uint) internal pure returns (uint) fp = g;
    return fp == g;          // solc: true
  }
  function eqDiff() external pure returns (bool) {
    function(uint) internal pure returns (uint) fp = g;
    return fp != h;          // solc: true
  }
}
```

**solc 0.8.35** — compiles; `eqSame()` returns `true` (word 1), `eqDiff()`
returns `true`. (Forge staticcall, both succeed with a bool payload.)

**solidity-lean** — reverts. The comparison lowers generically to
`Expr.binary BinaryOp.eq/ne` (Interface.lean:9677 rewrites both operands; no
special function-comparison lowering exists), which routes through
`BinaryOp.apply` (Interpreter.lean:6362). The `eq`/`ne` arms of `BinaryOp.apply`
handle only `Value.word`, `Value.int`, and `Value.externalFunction`; an
`internalFunction` operand falls through to `_, _ => Except.error
RevertData.typeMismatch` (= `RevertData.panic 0`).

Direct interpreter `#eval` (definitive):
```
BinaryOp.apply true BinaryOp.eq (Value.internalFunction 1) (Value.internalFunction 1)
  => Except.error (RevertData.panic 0)          -- solc: word 1
BinaryOp.apply true BinaryOp.ne (Value.internalFunction 1) (Value.internalFunction 2)
  => Except.error (RevertData.panic 0)          -- solc: word 1
BinaryOp.apply true BinaryOp.eq (Value.externalFunction 5 7) (Value.externalFunction 5 7)
  => Except.ok (Value.word 1)                   -- external path works
```

**Root cause**
- `SolidCore/Solidity/Interpreter.lean:5670-5683` (`eq`) and `5684-5697` (`ne`):
  arms for `word`/`int`/`externalFunction` only; missing a
  `Value.internalFunction id₁, Value.internalFunction id₂` arm. Fallthrough at
  5683 / 5697 is `typeMismatch`.
- The typechecker *accepts* the comparison:
  `SolidCore/Solidity/TypeCheck.lean:3467` — `Ty.isEqualityComparable` returns
  `true` for `functionWithLocations _ _ _ _ _ _` (both internal and external
  visibilities). So this is not an over-reject at type-check time; it is a
  spurious runtime revert on a well-typed program.

**Reachability** — the value model guarantees the fault triggers: a local `fp`
of internal-function type reads as `Value.internalFunction id`, and a bare
function reference `g` is rewritten to its dispatch-ID and lowered to
`Expr.internalFunction id` → `Value.internalFunction id`
(Interface.lean:7141-7146). Whichever operand shapes result, at least one
operand of `==`/`!=` is a `Value.internalFunction`, and there is no
`BinaryOp.apply` arm that admits it, so the comparison always reverts. The fix
is a one-arm addition comparing the two IDs with `wordEq` (mirroring the
external arm). This is clearly an oversight (typechecker + default-value model +
external arm all support function equality), not an intentional out-of-scope
abstraction.

## Clean negatives (verified agreement — no divergence)

All checked against solc 0.8.35 via Forge and against the Lean model:

1. **`.selector`** — `this.foo.selector` for `foo(uint256)` = `0x2fbebd38`;
   public-getter selector `this.x.selector` = `x()` = `0x0c55699c`. solidity-lean
   computes from the canonical signature via `Keccak.selector4`
   (ABI.lean:57 `selectorFromSignature`, Interface.lean:3926
   `externalFunctionSignature?`). Canonicalisation of exotic param types is
   correct: enum→`uint8`, contract/UDVT (`Ty.user`)→`address`, external function
   type→`function` (Interface.lean:2477-2479). Match.

2. **External function value = address(20)++selector(4), left-aligned in a
   32-byte ABI word.** solc `abi.encode(this.foo)` yielded
   `2e234dae…470b` ++ `2fbebd38` ++ 8 zero bytes. solidity-lean encodes
   identically: Interpreter.lean:4591-4596 (`address ++ selector ++
   replicate 8 0`). `.address` (right-aligned 20-byte address) and `.selector`
   extraction match (Interpreter.lean:6202, member handling Interface.lean:4275,
   6600). Match.

3. **Uninitialized / deleted internal function pointer call → Panic(0x51).**
   solc: both `callUninit()` and `callDeleted()` revert with
   `0x4e487b71…0051`. solidity-lean: `Stmt.internalCallPtr` resolves the ID
   against the table; a miss (including ID 0 = uninitialised/deleted) reverts
   `RevertData.panic 0x51` (Interpreter.lean:8566-8568). Match.

4. **Normal dispatch through a pointer** — `fp = g; fp(5)` returns 6 on both.

5. **External function-value equality** compares address AND selector
   (Interpreter.lean:5676-5682 / 5690-5696). Match.

6. **State-mutability covariance for function-type assignment.** Full solc
   accept/reject matrix reproduced (internal + external payable), all 11 cases
   agree with `StateMutability.canImplicitlyConvertFunction`
   (TypeCheck.lean:1033-1047):
   - ACCEPT: pure→view, pure→nonpayable, view→nonpayable, payable→nonpayable (ext).
   - REJECT: nonpayable→view, nonpayable→pure, view→pure, nonpayable→payable,
     payable→view, pure→payable.
   Param/return types required exactly equal, visibility required equal
   (TypeCheck.lean:1093-1099) — matches solc's invariant param/return typing.
   Match.

## Out-of-scope / notes

- **Internal function-pointer VALUE representation.** solidity-lean models the
  pointer as an abstract sequential dispatch ID (`Value.internalFunction id`,
  Interpreter.lean:75-84), explicitly the via-IR dispatch-ID model, NOT the
  legacy-codegen code-offset (jump-tag) value. Under legacy codegen the concrete
  numeric value of a stored internal function pointer is a compilation-dependent
  code offset; solidity-lean cannot and does not reproduce that exact integer.
  This is only observable by reading the raw storage/stack bits of a pointer via
  assembly, is inherently bytecode-dependent, and is a deliberate abstraction —
  not a divergence in any semantically-defined observation (dispatch, equality,
  ABI encoding of external fns are all defined and checked above).

- Not exhaustively tested (judged lower risk, model reads correct):
  `super.f.selector`, selector of an overloaded function chosen by argument
  context (solidity-lean resolves via `externalFunctionSignature?` on the
  resolved `paramTys`, which is the correct discriminator), library/free-function
  selectors, and arrays of internal function pointers. No divergence found on
  inspection; flagged as untested rather than cleared.
