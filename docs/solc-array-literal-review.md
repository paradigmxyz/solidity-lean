# Divergence review: inline array literals `[a, b, c]` — solidity-lean vs solc 0.8.35

Search-only review. Ground truth: pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`), legacy codegen.
solidity-lean behavior confirmed empirically by `#eval`-ing the type checker
(`SolidCore.Solidity.ContractDecl.typechecked?`) on hand-built ASTs.

## Headline

**One real divergence family, HIGH confidence (~95%), severity = OVER-ACCEPT.**

solidity-lean accepts assigning/returning/passing an inline array literal to a
**fixed-size array target whose element type is wider than (or otherwise differs
from) the type solc infers bottom-up for the literal**, as long as each raw
literal element numerically fits the target element type. solc rejects every
such program because it computes the array-literal type independently (the
smallest common mobile type, e.g. `uint8[3]`) and then forbids implicit
**fixed-array element-type conversion** (`ArrayType::isImplicitlyConvertibleTo`
requires an equal element type for memory arrays).

This is exactly the "uint8[3] → uint256[3] gotcha" called out in the mission
(#3).

## Root cause

Two cooperating facts in `SolidCore/Solidity/TypeCheck.lean`:

1. **Number-literal element type is always `uint256`, not the smallest fit.**
   `literalTy?` (TypeCheck.lean:4156-4159) maps `Literal.number _ ↦ Ty.uint 256`.
   (Executable mirror: `Literal.abiTy?`, Interface.lean:3786.) So solidity-lean
   never forms solc's bottom-up `uint8[3]` literal type.

2. **The fixed-array assignability check is target-directed and element-wise.**
   `checkExprAssignableTo` (TypeCheck.lean:8268-8279) special-cases
   `Expr.array … : Ty.array _ (some size)` and, before any real type check, asks
   `exprContextuallyAssignableTo`. That routine
   (`exprContextuallyAssignableToFuel`, TypeCheck.lean:4946-4974) recurses into a
   fixed-array target and checks **each raw element against the *target* element
   type** via `exprIsUntypedImplicitLiteralExpression … && implicitLiteralFits
   expected element` (lines 4950-4955, 4972-4973). A bare `1` "fits" `uint256`,
   so `[1,2,3]` is judged assignable to *any* `uintN[3]` it fits — bypassing the
   `expectAssignableToIn` reject that would otherwise fire.

solc has no such target-directed relaxation for inline arrays: the literal's
type is fixed at analysis time and fixed→fixed array conversion needs identical
element types.

## Confirmed cases (solc run + `typechecked?` eval)

| program (inside `function f() public pure`) | solc | solidity-lean | verdict |
|---|---|---|---|
| `uint8[3] memory x = [1,2,3];` | ACCEPT | ACCEPT | match |
| `uint16[3] memory x = [1,2,3];` | **REJECT** (`uint8[3]` ↛ `uint16[3]`) | **ACCEPT** | **DIVERGE (over-accept)** |
| `uint256[3] memory x = [1,2,3];` | **REJECT** | **ACCEPT** | **DIVERGE (over-accept)** |
| `uint256[2][2] memory x = [[1,2],[3,4]];` | **REJECT** (`uint8[2][2]`) | **ACCEPT** | **DIVERGE (over-accept)** |
| `function f() returns (uint256[3] memory){ return [1,2,3]; }` | **REJECT** | **ACCEPT** | **DIVERGE (over-accept)** |
| `uint8[2][2] memory x = [[1,2],[3,4]];` | ACCEPT | ACCEPT | match |

solc rejects the argument-position analogue too (`g([1,2,3])` where `g` takes
`uint256[3] memory`: "Invalid implicit conversion from uint8[3] memory to
uint256[3] memory"); the same contextual path drives argument checking, so it is
over-accepted for the same reason (not separately re-`#eval`ed, ~85% conf).

## Cases where solidity-lean is CORRECT (clean negatives, all verified)

- **Empty literal** `uint8[0] memory x = [];` — both REJECT. solc: "Unable to
  deduce common type for array elements"; solidity-lean: arity/`empty array
  literal` (TypeCheck.lean:7078-7079, 8272-8273). Match.
- **Ragged nested** `uint8[2][2] memory x = [[1],[2,3]];` — both REJECT. solc:
  "Unable to deduce common type"; solidity-lean: inner `uint256[1]` vs
  `uint256[2]` have no `commonImplicit?` → "array literal common type". Match.
- **Fixed → dynamic** `uint256[] memory x = [1,2,3];` — both REJECT (dynamic
  target has `size = none`, so the contextual fixed-array path does not apply and
  `uint256[3] ↛ uint256[]`). Match. (solc also rejects `[uint(1),2,3]` into
  `uint256[]` — fixed→dynamic memory copy is not implicit.)
- **Same-element-type nested** `uint8[2][2] = [[1,2],[3,4]]` — both ACCEPT.
- **Element that overflows the target** `uint8[2] memory x = [1,256];` — both
  REJECT (256 ∤ uint8; contextual element check fails, then `uint256[2] ↛
  uint8[2]`). Match.

Net: solidity-lean gets the reject/accept right in every case where the target
element type equals solc's bottom-up literal element type, and in the
empty/ragged/dynamic/overflow rejects. It **only** diverges when the target
element type is strictly wider than solc's inferred literal type — then it
over-accepts.

## Notes / non-divergences

- No **wrong-value** exposure: the over-accepted programs would store the same
  numeric values (widened), so this is purely an acceptance-surface divergence.
- Element **common-type width/sign inference (#1)** is not independently
  observable here because solidity-lean uses `uint256` for every numeric literal
  element and the accept/reject is decided by the target-directed path above; I
  found no case where the *inferred* width alone (absent an explicit target)
  produces a divergent runtime value.
- Mapping-typed inline array (`[m]`) correctly rejected (TypeCheck.lean:7091-7095).

## Suggested fix direction (not applied — search-only)

Make the fixed-array-literal contextual path enforce solc's rule: require the
target element type to equal the literal's independently-computed common element
type (identity for memory fixed arrays), rather than accepting any target the raw
elements individually "fit". Equivalently, drop the `implicitLiteralFits`
element-wise shortcut for `Expr.array` targets and route through
`expectAssignableToIn` with the bottom-up literal type. Root anchors:
TypeCheck.lean:4950-4955 and 8270-8279.
