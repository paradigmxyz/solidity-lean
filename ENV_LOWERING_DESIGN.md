# ENV_LOWERING_DESIGN — R2: unify env-less and env-aware lowering (rearch phase 3)

Branch `rearch/env-lowering-unify`, base `8f0f3d3` (post R1 + R3).

## Problem

`SolidCore/Solidity/Interface.lean` carried TWO parallel expression lowerings:

1. **Env-less** `Expr.toCore?` / `Expr.toCoreAs?` / `Stmt.toCore?` — no type
   environment, so it cannot emit the operand-width checked-overflow cleanup
   (`uintCleanup`/`intCleanup`). Narrow (`uintN`/`intN`, N<256) checked
   arithmetic lowered through it silently loses Panic 0x11 (and, in
   `unchecked`, computes at 256 bits where the EVM wraps at the narrow width —
   a wrong VALUE, not just a missing panic; see `uncheckedWhile` below).
2. **Env-aware** `Expr.toCoreAsWithEnv?` — not a real recursion but a stack of
   shape interceptors (H2 narrow-cast, NEG-NARROW, ternary, TC1 abi ternary…)
   in front of `Expr.toCoreAsWithEnvDirect?`, which itself tries the env-less
   `toCoreAs?` first. Child positions (binary operands, `&&`/`||`/`!`
   subtrees, index keys) stopped at `Direct?` and lost the interceptors.

Any statement position calling the env-less path as PRIMARY (loop conditions,
plain `assert`, discard statements) lost the cleanup entirely.

## Stage A — empirical baseline (solc 0.8.35 + Forge real EVM vs model)

Probe: `tests/forge-harness/cond-narrow-cleanup` (22 Forge tests, all PASS on
the real EVM) + `CheckedInput.ownCall` on the imported contract. uint8
`a=200,b=100` (a+b=300 overflows), int8 `a=-100,b=-50` (a+b=-150 underflows).

| # | construct | example | real EVM | model @8f0f3d3 | after B+C |
|---|-----------|---------|----------|-----------------|-----------|
| 1 | while cond | `while ((a+b) < 250)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 2 | for cond | `for (…; (a+b) < 250; …)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 3 | do-while cond | `do {…} while ((a+b) < 250 && …)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 4 | plain comparison | `return (a+b) < 250;` | Panic 0x11 | ok (env path) | ok |
| 5 | if cond | `if ((a+b) < 250)` | Panic 0x11 | ok (env path) | ok |
| 6 | require cond | `require((a+b) < 250)` | Panic 0x11 | ok (env path) | ok |
| 6b | assert cond | `assert((a+b) < 250)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 7 | discard stmt | `a + b;` | Panic 0x11 | **no panic** | Panic 0x11 |
| 8 | eq comparison | `return (a+b) == 44;` | Panic 0x11 | ok | ok |
| 9 | `&&`-wrapped cmp in if | `if ((a+b) < 250 && a > 0)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 10 | `!`-wrapped cmp in if | `if (!((a+b) < 250))` | Panic 0x11 | **no panic** | Panic 0x11 |
| 11 | index key | `arr[a + b]` | Panic 0x11 | **no panic** | Panic 0x11 |
| 12 | internal call arg | `inner(a + b)` | Panic 0x11 | ok | ok |
| 13 | `&&`-wrapped cmp in while | `while ((a+b) < 250 && k < 3)` | Panic 0x11 | **no panic** | Panic 0x11 |
| 14 | int8 while cond | `while ((a+b) > -100)` | Panic 0x11 | **no panic** | Panic 0x11 |
| C1 | safe while | a=3,b=4 | 3 | ok | ok |
| C2 | safe cmp | a=3,b=4 | true | ok | ok |
| C3 | unchecked cmp | `unchecked { (a+b) < 250 }` | true (wraps→44) | ok | ok |
| C4 | unchecked while | `unchecked { while ((a+b)<250 && k<3) }` | 3 (wraps→44, loops) | **0 — WRONG VALUE** (add ran at 256 bits, 300<250 false) | 3 |
| C5 | truncating cast | `uint8(300) < 250` | true (44) | ok | ok |
| C6 | safe index / call arg | | 9 / 44 | ok | ok |

**Verdict:** comparison operands in general were NOT implicated — the plain
comparison/if/require positions already routed env-aware
(`conditionUseCoreWithInternalCalls?` binary arm / `returnValuesCoreWithReturnTys?`).
The gap was (a) statement positions whose PRIMARY was `Expr.toCore?`
(while/for/do-while conditions, non-call `assert`, discard statements), and
(b) expression CHILD positions the interceptor stack never reached
(`&&`/`||`/`!` subtrees, index keys).

## Stage B — one type-directed recursion (commit `4682e29`)

`Expr.toCoreAsWithEnv?` / `Expr.binaryToCoreWithEnvTyped?` /
`Expr.binaryToCoreWithEnv?` are now thin wrappers over a mutual,
**fuel-bounded** recursion:

- `Expr.toCoreAsWithEnvFuel?` — the old interceptor body, with every child
  recursing back into the FULL env-aware lowering: ternary cond/branches,
  binary operands (via `binaryToCoreWithEnvTypedFuel?`), H2 cast peels,
  NEG-NARROW inner, plus NEW arms:
  - `&&`/`||`: both operands at `Ty.bool` (in `binaryToCoreWithEnvTypedFuel?`);
  - `!`: operand at `Ty.bool` (bool-targeted only);
  - `Expr.index`: a NARROW-typed key is lowered env-aware at its own type
    (checked cleanup → Panic 0x11) and plugged into
    `Expr.indexReadCoreBuilder?` (moved earlier in the file; it mirrors the
    `Expr.index` arms of `Expr.toCore?` exactly). Wide keys keep the env-less
    path — core arithmetic already checks at 256 bits, so only narrow keys
    diverged, and gating avoids emission churn.
- `Expr.toCoreAsWithEnvBitAwareFuel?` — bit-aware wrapper; non-bit-op shapes
  now recurse into the full lowering instead of stopping at `Direct?`.

**Why fuel, not `sizeOf`:** the H2/NEG arms reach children through
`peelToOverflowArithmetic?`/`peelToNarrowNeg?` (functions, not structural
projections), which `termination_by sizeOf` cannot see. Fuel = 1024 (matches
`defaultAnnotateAbiFuel`); at fuel 0 the lowering degrades to
`toCoreAsWithEnvDirect?` (today's fallback) — never a new reject.

**Interceptors:** none were deleted as separate functions — they were already
arms of `toCoreAsWithEnv?` (H2, NEG-NARROW, ternary, TC1, fn-pointer literal)
and remain as arms of the unified recursion; what changed is that they are now
REACHABLE FROM EVERY CHILD position instead of top-level-only. The
NarrowCleanupFamily / structCtor / push interceptors at statement level are
untouched (their witnesses still pass through the new path).

## Stage C — statement positions routed env-aware (commit see log)

New helper `Expr.conditionCoreWithEnv?` = env-aware at `Ty.bool` first,
env-less `Expr.toCore?` fallback (acceptance-preserving; `none` only when both
fail, i.e. call-bearing conditions → existing call-hoisting desugars).

Routed through it:
- `Stmt.whileLoop` / `Stmt.doWhile` / `Stmt.forLoop` call-free conditions in
  `Stmt.toCoreWithInternalCalls?` (for-loop under `loopEnv`, so the for-init
  bindings are in scope);
- `conditionUseCoreWithInternalCalls?` unary arm, catch-all arm, and the
  binary arm's fallback (if/require and the hoisted-loop check paths);
- NEW `assert(<non-call cond>)` arm (mirrors `require`; prior generic
  fallbacks preserved verbatim on `none`);
- NEW discard-expression arm (`Stmt.expr` of binary / `-x` / `~x` / `!x`)
  lowering at the expression's own `abiTyWithEnv?` type.

## Remaining legitimate env-less callers (each justified)

- `Expr.toCore?` as the LEAF WORKHORSE under `toCoreAsWithEnvDirect?` /
  `coreAsFromTy?`: the env path resolves the TYPE and applies the target-width
  conversion/cleanup on top of the env-less core. This is by design (the type
  is applied at the boundary); it is only wrong when an INTERIOR node needed a
  type, which is exactly what the Stage B recursion now catches at the shapes
  where it matters (binary/unary/ternary/cast/index/bool ops).
- Call-condition fallbacks in `conditionUseCoreWithInternalCalls?`
  (`Expr.call ident/member` arms): the cond is a CALL; toCore? only lowers
  builtin-ish calls there. Builtin call ARGUMENTS are still env-less (debt, below).
- `Stmt.toCore?` as the fallthrough of `Stmt.toCoreWithInternalCalls?` for
  arms with no env-relevant expression positions (emit/revert/etc.) and as the
  none-fallback everywhere (acceptance preservation).
- The importer/constant-folding/getter-generation paths (`Expr.toCore?` on
  synthesized literals, selectors, defaults): genuinely type-free.
- TC1 `abi.encode` ternary branch lowering still uses the non-fuel
  `toCoreAsWithEnvBitAware?` (leaf `Direct?`): pre-existing behavior kept
  byte-identical; abi args are a separate lowering family (debt, below).

## Stage D — status: NOT attempted (debt recorded)

Deliberately deferred to keep the gate green; the env-less EXPRESSION path is
subsumed at the divergent positions, which was the core deliverable.

- `Stmt.toCoreWithInternalCalls?` remains a ~50-arm dispatch; most arms still
  fall back to `Stmt.toCore?`. Collapsing them into a uniform env-aware
  fallthrough is the next phase.
- Builtin/external call ARGUMENTS and `abi.encode*` arguments still lower
  env-less (`Args.toCoreExprs?` / `toAbiEncodeArg?`) — narrow checked
  arithmetic inside e.g. `keccak256(abi.encodePacked(a+b))` (uint8) is a
  candidate residual; internal call args are env-aware (probe #12 ok).
- LVALUE index keys (`arr[a+b] = v`) still lower via `Expr.toCoreLValue?`
  (env-less); only the READ side is fixed. Candidate follow-up probe.
- `<<`/`>>` still fall to the Direct path (pre-existing FB1 handling).
- `toCoreFixedBytesBitOp?` leaves fall to `Direct?` (bytesN subtrees rarely
  contain narrow int arithmetic that survives typing; kept to avoid churn).
- The duplicated depth-2 `address(T(inner))` arm (~4374/~5060 env-less
  `toCore?`) was NOT touched: it did not fall out of Stage B (it lives in the
  env-less pass, which remains as the leaf workhorse) — factoring it is
  cosmetic and deferred with Stage D.

## Proof surface

`FuelMonotonicity.lean` / `AdoptionLaws.lean` do not reference the lowering
functions (they pin the interpreter/eval layer) — no proof changes expected;
full `lake build` is the gate. Witness `#guard`s that inspect emitted core are
written cleanup-tolerant (they recurse through `uintCleanup`).

## Fix-forward: literal-only constant expressions (uniswap-v2 regression)

The full 257-case gate flipped `uniswap-v2-libraries` (encode: `z =
uint224(y) * Q112`, `Q112 = 2 ** 112`). After constant inlining the RHS
reaches the env-aware lowering, whose `**` arm types the base at its MOBILE
type (`2` -> `uint8`); the operand-width cleanup then emitted
`uintCleanup 224 (uintCleanup 8 (exp 2 112))` -> spurious Panic 0x11. solc
evaluates literal-only expressions at COMPILE TIME as unbounded rationals
(`RationalNumberType`) and checks only the FINAL value against the target
type - exactly what the env-less `toCore?`/`toCoreAs?` folding does. Fix
(commit `c20e979`): (1) `toCoreAsWithEnvFuel?` routes any
`isRawNumberLiteralExpression` straight to `toCoreAsWithEnvDirect?` (constant
folding; non-fitting constants keep failing closed), except at
internal-function-typed targets (rewritten fn-pointer dispatch-ID literals);
(2) `binaryToCoreWithEnvTypedFuel?` returns `none` when BOTH operands are raw
literals (callers fall back to folding). Verified: `2**112` at `uint224` now
folds to the word via the env path; Enc2 probes (constOnly / encodeLocal /
encodeExpr / castOnly / mulPlain) match the real EVM; uniswap-v2-libraries
`forge=ok lean=ok`; all 22 EnvLoweringUnify pins unchanged.

## Witness / lane

- `SolidCore/Witness/EnvLoweringUnify.lean` (imported from `SolidCore.lean`):
  22 `#guard` pins — all Stage-A divergents now Panic 0x11 / correct values,
  plus truncating-cast, unchecked-wrap, and safe controls.
- Forge lane `tests/forge-harness/cond-narrow-cleanup` + manifest entry
  `cond-narrow-cleanup` (22 real-EVM tests + 23 Lean evals).
