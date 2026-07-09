# Short-circuit boolean & control-flow divergence review vs solc 0.8.35

**Scope:** short-circuit `&&`/`||`, ternary, `if`/`else`, `while`/`do-while`/`for`,
`break`/`continue`, `return` in loops, unreachable code, break/continue-outside-loop.

**Ground truth:** pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) + Forge, legacy
codegen (optimizer=false, no via_ir).

**Verdict: CLEAN NEGATIVE — no divergence found (confidence 95%).**
Every construct in scope matches solc/EVM behavior both by code inspection and by
differential execution (real EVM via Forge vs the Lean interpreter run on the
same contract imported from solc's AST). This is a mature area with pre-existing
harness coverage; I added and ran a fresh combined probe covering the gaps.

---

## Root-cause code inspection (solidity-lean)

All file refs are `SolidCore/Solidity/Interpreter.lean` unless noted.

### 1–2. `&&` / `||` are genuinely short-circuited (NOT eager)
`Expr.binary BinaryOp.boolAnd` (6327–6338) and `boolOr` (6339–6350) in the runtime
evaluator evaluate the lhs, then evaluate the rhs **only** when the lhs does not
decide the result; the un-taken rhs is never evaluated and its runtime state is
not threaded:
- `boolAnd`: if `!wordTruthy lhs` → `pure (Value.word 0, runtime')` (rhs skipped).
- `boolOr`: if `wordTruthy lhs` → `pure (Value.word 1, runtime')` (rhs skipped).

These two cases sit **before** the generic `Expr.binary op lhs rhs` case (6351),
which evaluates both operands eagerly then calls `BinaryOp.apply`. Lean matches
top-to-bottom, so bool ops never reach the eager path.

`BinaryOp.applyWord` (5608–5609) does contain an eager
`wordTruthy lhs && wordTruthy rhs`, but it is **dead code for bool ops** — it
only ever combines already-evaluated words for the non-short-circuit fallback and
is never reached for `boolAnd`/`boolOr`. No double-evaluation of side effects.

### 3. Precedence/associativity
Parsing/lowering is upstream of the interpreter; the differential tests below
exercise chained/mixed forms and all matched solc.

### 4. Ternary — untaken branch not evaluated
`Expr.ternary` (6697–6706): evaluates `cond`, then evaluates **only** the selected
branch. Nested ternaries recurse, so only the taken leaf is evaluated.

### 5. `if`/`else`
`Stmt.ifElse` (~8589): evaluates cond once, runs the taken branch only.

### 6. Loops — ordering
Control flow is a `Result` sum type (`normal`/`returned`/`selfdestructed`/
`reverted`/`broke`/`continued`, 7483–7497); `Stmt.evalList` (8954–8961) stops on
any non-`normal`.
- **while** `evalWhile` (8963–8986): cond checked **first**; body; `continued`→re-loop
  (back to cond); `broke`→`normal`; return/revert propagate.
- **do-while** `evalDoWhile` (8988–9021): body runs **first**, then cond checked;
  `continued`→checks cond (jumps to condition); `broke`→`normal`.
- **for** `evalFor` (9023–9052), entered from `Stmt.forLoop` (8617–8623) which
  pushes/pops a scope for `init` (so loop-init vars are loop-scoped): cond→body→post
  →repeat. `init` runs exactly once.

### 7. `break`/`continue`
`Stmt.break`→`Result.broke` and `Stmt.continue`→`Result.continued` (8889–8890),
consumed by the innermost loop evaluator only (nested loops naturally affect the
inner loop). **CRITICAL — `for` + `continue` runs the post-expression:** in
`evalFor` the `Result.continued` arm (9041–9045) runs `Stmt.eval ... post` before
recursing, exactly like the `Result.normal` arm. Matches solc.

Break/continue **outside a loop → rejected**: `TypeCheck.lean` tracks
`loopDepth` (1629, incremented at 1731) and requires `loopDepth > 0` for
`Stmt.break`/`Stmt.continue` (9473–9477), else `breakOutsideLoop`/
`continueOutsideLoop` (332–333).

### 8. `return` inside loops
`Result.returned` is not special-cased by the loop evaluators, so it falls through
the `| result => pure result` arm and propagates out of the loop and the function.

### 9. Unreachable code after `return`/`revert`
No reachability/dead-code rejection in `TypeCheck.lean` (no `unreachable`/`deadCode`
`TypeError`; `checkStmtSeq` type-checks every statement with no terminator gating).
Contract with unreachable code **accepted** — matches solc (warning only, compiles).

---

## Differential execution evidence

### Pre-existing harness cases (re-run, pinned solc 0.8.35) — all PASS
- `expression-control` — `false && (x=1)`, `true || (x=2)`, `true && (x=x+3)`,
  `false || (x=x+5)` side-effect suppression + `flag ? (x=7) : (x=9)` ternary
  side-effect select. `forge=ok lean=ok`, compare=pass.
- `loop-control` — while/for `continue`+`break` (whileSum/forSum), and
  `solc_rejects=ok` for `BreakOutsideLoop.sol` / `ContinueOutsideLoop.sol`
  (both solc and the Lean checker reject). `forge=ok lean=ok`, compare=pass.
- `branch-require` — if/else + require/assert. `forge=ok lean=ok`, compare=pass.

### New combined probe (this review) — EVM (Forge) and Lean interpreter agree on all
Contract `ProbeTarget` (scratchpad `probe/src/Probe.sol`). Forge tests all 8 green
against real EVM with solc 0.8.35; the same source imported from solc's AST and run
through the Lean type-checker + interpreter returns `Except.ok true` for each
(and `importedContractAccepted = true`):

| function | input | EVM result | Lean result | property exercised |
|---|---|---|---|---|
| `doWhileContinue` | 3 | 4 | 4 | do-while body runs ≥1×; `continue` jumps to cond |
| `nestedBreakContinue` | — | 3030 | 3030 | break/continue affect innermost loop only |
| `returnInLoop` | — | 203 | 203 | `return` in nested loop exits whole function |
| `unreachableAfterReturn` | — | 42 (compiles) | 42; contract accepted | unreachable code accepted, not rejected |
| `chainedShortCircuit` | — | 2052 | 2052 | chained `a&&b&&c` / `a\|\|b\|\|c` suppress later side effects |
| `nestedTernary` | 0 | 101 | 101 | nested ternary evaluates only the taken leaf |
| `nestedTernary` | 1 | 202 | 202 | " |
| `nestedTernary` | 2 | 303 | 303 | " |

`chainedShortCircuit` is the sharpest short-circuit witness: `((x=1)==1) &&
((x=2)==0) && ((x=3)==3)` leaves `x==2` (third operand never assigns 3), and
`((y=5)==5) || ((y=6)==6) || ((y=7)==7)` leaves `y==5` (second/third never
evaluated) — both EVM and the Lean interpreter produce `x*1000+y*10+... = 2052`.

---

## Conclusion
No divergences in short-circuit boolean evaluation or control-flow statements
against solc 0.8.35. The eager `BinaryOp.applyWord` bool combiner (5608–5609) is
dead code for bool ops and does not cause eager side-effect evaluation. Highest-risk
behaviors — short-circuit side-effect suppression (#1/#2), ternary untaken-branch
suppression (#4), and `for`+`continue` running the post-expression (#7) — are all
correct and empirically confirmed against real EVM.
