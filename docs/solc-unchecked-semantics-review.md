# solc `unchecked { }` block semantics — adversarial review

Scope: the `unchecked` FLAG propagation and the exact operator set it affects at
RUNTIME, in solidity-lean (`SolidCore/Solidity/Interpreter.lean`,
`Interface.lean`) vs pinned solc 0.8.35 (`47b9dedd`, LEGACY/via-IR cross-check).

**Verdict: rigorous CLEAN NEGATIVE.** No divergence found. Every axis the task
flags — block scope, callee isolation, operator set, div/mod-by-zero survival,
`**` wrapping, signed neg / signed-min-div wrapping, `<<=` cleanup, conversions,
constant overflow — matches solc exactly. Details and evidence below so a
re-review can re-check each claim, not re-derive it.

## Mechanism in solidity-lean

The checked-ness is a single `Bool` on `Context` (`context.checked`), threaded
lexically:

- `Stmt.checked body` → evaluate body with `{ context with checked := true }`
  (Interpreter.lean:8868-8869).
- `Stmt.unchecked body` → `{ context with checked := false }`
  (Interpreter.lean:8870-8871).

Every arithmetic site reads `context.checked` and passes it into the `checked*`
primitives (`BinaryOp.apply context.checked …` at 6261, 6285, 6339; increment/
decrement at 5926, 5939-5940; unary at 6192). The `checked*` primitives
(5371-5559) branch on that flag: `checked && overflow → Except.error
RevertData.overflow`, else wrap.

## Axis-by-axis verification

### 1. Block scope is lexical/syntactic — PASS
`context.checked` flows to every sub-statement/sub-expression uniformly. A
`for`-loop increment is just a statement evaluated under the ambient context, so
`unchecked { for(...) i++ }` makes `i++` unchecked and `for(...){ unchecked{} }`
leaves `i++` checked — structurally correct. Nested `unchecked` is idempotent
(inner block re-sets `checked := false`).

### 2. Callee isolation — PASS (verified)
Internal calls reset the flag: `Stmt.internalCall` and `Stmt.internalCallPtr`
both evaluate the callee body with `{ context with checked := true }`
(Interpreter.lean:8510-8511, 8539-8541), regardless of the caller's block.
- solc evidence: a function called from inside `unchecked { }` still compiles its
  own body with `checked_add_t_uint256` (T.sol `leak`→`callee`: `fun_callee_82`
  emits `checked_add_t_uint256`, IR line 460-472). No leak in either direction.

### 3. Operator set affected by `unchecked` — PASS

| op | solidity-lean | solc 0.8.35 |
|---|---|---|
| `+ - *` (uint) | `checkedAdd/Sub/Mul checked` (5371-5392) | `checked_*`/`wrapping_*` |
| `+ - *` (int) | `checkedSigned*` via `checkedSignedWord` (5464-5489) | same |
| unary `-` (intN) | `checkedSignedNeg checked` (5491-5494) — wraps unchecked | `negate_wrapping_t_int8` under unchecked (D/T evidence) |
| `**` (uint & int) | `checkedExp`/`checkedSignedExp checked` (5446-5453, 5527-5545) — **wraps** unchecked | `cleanup_t_uint8(exp(base,exp))` under unchecked (T.sol IR 318-320) |
| `++ / --` | `applyIncDec[Cleanup] … context.checked` (5921-5945) | same |
| compound `+= …` | `BinaryOp.apply context.checked` (6261, 6285) | same |
| `/ %` and div/mod-by-zero | `checkedDiv/Mod` ignore checked, **always** panic 0x12 (5394-5406) | `wrapping_div_t_int8`: `if iszero(y){panic_error_0x12()}` still present under unchecked (T.sol IR) |
| signed `type(intN).min / -1` | overflow **only when** `checked` (5502-5509) — wraps unchecked | `wrapping_div_t_int8` uses plain `sdiv`, no overflow check → wraps (T.sol `sdivMinUnchecked`) |
| shifts `<< >> `, bitwise `& | ^ ~`, comparisons, `!` | never read `checked` (5571-5586, 5610-5636, 5718-5729) | shift/bitwise never overflow-checked |
| `addmod/mulmod` mod-0 | `checkedAddMod/MulMod` always panic 0x12 (5547-5559) | unaffected |

### 4. `<<=` compound-assign cleanup — PASS (subtle, handled)
Left shift truncates to the operand width with NO overflow check even in a
checked block. solidity-lean special-cases the compound-assign cleanup:
`cleanupChecked := match op | shl => false | _ => context.checked`
(Interpreter.lean:6289-6293).
- solc evidence: `x <<= n` for `uint8 x` in a *checked* function compiles to
  `shift_left_t_uint8_t_uint8` = `cleanup_t_uint8(shift_left_dynamic(...))` — a
  masking truncation, no `if iszero(eq(...)) revert` (T.sol IR
  `shift_left_t_uint8_t_uint8`). Match.

### 5. Explicit narrowing conversions — PASS
`unchecked` does not touch conversions; they truncate regardless. The importer
routes explicit conversions to `uintCast`/`intCast` (no `checked` param,
Interpreter.lean:597-655, always truncate) and only the overflow-checked
*arithmetic-result* narrowing to `uintCleanup`/`intCleanup` (which thread
`context.checked`, 625-672). The distinction is explicit in
Interface.lean:3416-3439. So `uint8(y)` masks in and out of `unchecked`, while a
narrow-typed arithmetic result panics only when checked — exactly solc.

### 6. Constant-expression overflow — PASS (CE-family, re-confirmed)
- `unchecked { return type(uint256).max + 1; }` is NOT a rational-constant
  expression (`type(uint256).max` is typed `uint256`), so solc emits a runtime
  `wrapping_add_t_uint256(0xff..ff, 1)` = 0 (C.sol IR, exit 0). solidity-lean
  imports it as a word add with `checked=false` → wraps to 0. Match.
- `unchecked { uint8 x = 255 + 1; }` IS rational-literal arithmetic (`int_const
  256`); solc **rejects at compile time** regardless of `unchecked`:
  "Literal is too large to fit in uint8" (D.sol, exit 1). Rational-literal
  folding is unaffected by `unchecked`; solidity-lean rejects at import
  (CE-family). Match.

## Observable-value spot checks (all consistent)
- `unchecked { type(uint256).max + 1 }` = 0.
- `unchecked { uint8(255) + 1 }` = 0 (8-bit wrap via `uintCleanup? false`).
- `unchecked { 0 - 1 }` (uint256) = 2^256-1 (`checkedSub` false → `subWord`).
- `unchecked { int8 x = -128; -x }` = -128 (`checkedSignedNeg` false → wrap).
- `unchecked { int8(-128) / int8(-1) }` = -128 (signed-min/-1 wrap under unchecked).
- div/mod-by-zero inside `unchecked` still panics 0x12.

## Evidence artifacts
solc IR generated with
`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35 --ir` on the T/C/D
contracts above (scratchpad). Key functions inspected: `fun_callee_82`
(checked_add persists across unchecked caller), `wrapping_div_t_int8`
(div-by-zero panic survives), `shift_left_t_uint8_t_uint8` (unchecked shl
cleanup), `negate_wrapping_t_int8`, `cleanup_t_uint8(exp(...))`.

## Confidence
High. The propagation is a single lexical flag with the correct reset at the
function-call boundary; the operator set and the two genuinely-subtle cases
(`<<=` cleanup applied unchecked in a checked block; signed-min/-1 division
wrapping only under unchecked while div-by-zero always panics) are both handled
correctly and confirmed against solc IR.
