# solc 0.8.35 vs solidity-lean — tuple assignment & destructuring review

Search-only divergence hunt over tuple assignment / destructuring. Ground truth:
pinned solc 0.8.35 + Forge (legacy codegen). solidity-lean run via the current
`codex/solidity-semantics-only` branch through the solc-AST importer +
typecheck + executable-checked interpreter (`tests/bc-audit-probes/drive.py`,
`CheckedInput.ownCall`). solc runtime confirmed with a Foundry project where noted.

## Methodology note (accept/reject surface)

solidity-lean's frontend is the **real solc AST** (the importer shells out to
solc). Any program solc **rejects** (parse or type error) yields no AST, so the
importer fails too — solidity-lean co-rejects *by construction*. Therefore
**over-accept is not reachable** for solc-rejected programs on this path, and the
reject-side probes (#5 arity, #6 mixed decl+assign, #7b 1-tuple) are trivially
aligned. The reachable divergence surface is **over-reject** (solc accepts +
runs, solidity-lean fails to typecheck/lower) and **wrong-value / wrong-order**.

## Divergence found

### D1 — OVER-REJECT: tuple-assignment LHS component indexed by an internal call

**Severity: over-reject. Confidence: 99%.** (Reproduced; root cause located; it
is the explicitly-out-of-scope sibling of the just-closed MI1 over-reject.)

A tuple **assignment** (not declaration) whose LHS has an array/mapping index
component whose **index/key is an internal function call** — `(a[f()], b) = …`,
`(m[k()], b) = …` — fails at Executable lowering with
`TypeError.unsupported "checked executable checked contract …"`, before any value
is produced. solc accepts and runs it.

Minimal program (solc ACCEPT + runs; solidity-lean REJECT):

```solidity
contract G {
    uint256[3] xs; uint256 public logv; uint256 z;
    function tick(uint256 v) internal returns (uint256) { logv = logv*10 + v; return 0; }
    function f() external returns (uint256, uint256, uint256) {
        (xs[tick(1)], z) = (3, 4);
        return (logv, xs[0], z);
    }
}
```

- **solc + Forge:** `f()` → `logv=1, xs[0]=3, z=4` (the index call `tick(1)` runs
  once).
- **solidity-lean:** `Except.error (TypeError.unsupported "checked executable checked contract G")`.

Generalizes (all solc-ACCEPT, all solidity-lean-REJECT), confirmed:
- mapping key = internal call: `(m[k()], z) = (8, 9);`
- array index call **and** RHS call together: `(xs[k()], z) = (r(), 9);`

Contrast — these **work** (so the trigger is specifically the *call-valued index
in a tuple LHS*):
- single (non-tuple) assign with call index: `xs[tick(1)] = 9;` → runs (this is
  what MI1 fixed).
- tuple LHS with a **param** index `(xs[i], ys[i]) = (3,4)` or **storage-read**
  index `(xs[idx], ys[idx]) = (3,4)` → run correctly (34).
- tuple LHS with **constant** indices + side-effecting **RHS** calls
  `(xs[0], ys[1]) = (rhs(3), rhs(4))` → runs correctly.

**Root cause.** `SolidCore/Solidity/Interface.lean`:
- flat tuple assignment lowers via `tupleAssignmentCore?` (≈ line 6026) →
  `TupleItems.toCoreLValueTargets?` (line 5955) → `Expr.toCoreLValue?` (line
  5910). The index arms (lines 5918–5932) lower the index with the **pure**
  `Expr.toCore?`, which has **no case for an internal call** and returns `none`,
  so the LValue — and then the whole contract — fails to lower
  (`SolidCore/Solidity/Checked.lean:18–24` emits the `unsupported` string).
- `Stmt.toCoreWithInternalCalls?` (line 13000) has internal-call hoisting arms
  for the tuple-assignment **RHS** (Stage B, lines 13022–13095) but **none** that
  hoists a call out of an **LHS index**. The MI1 fix
  (`docs/DECISIONS.md` 2026-07-09 MI1) added hoisting arms only for the
  single-assignment lvalue `Expr.assign (Expr.index base (call)) …` and the
  `Stmt.returnValues (Expr.index base (call))` rvalue — the tuple-LHS index path
  was deliberately left out ("deliberately not widened here"). D1 is that
  residual.

**Impact on probe #9 (eval order).** Because solidity-lean over-rejects the
call-indexed tuple LHS, the RHS-vs-LHS-index ordering cannot be compared for that
shape. For reference, solc's order (measured on Forge) for
`(xs[tick(1)], ys[tick(2)]) = (rhs(3), rhs(4))` is `logv = 3412`: RHS components
left-to-right (`rhs(3)`, `rhs(4)`), **then** LHS index expressions left-to-right
(`tick(1)`, `tick(2)`). For **pure/param/storage-read** indices (which
solidity-lean does accept) no ordering divergence was observed.

## Clean negatives (solidity-lean matches solc)

All confirmed on this branch; solc side = pinned 0.8.35.

| # | Construct | Program (sketch) | solc | solidity-lean |
|---|-----------|------------------|------|-----------|
| 1 | Storage swap | `(a,b)=(b,a)` | 20,10 | 20,10 ✓ |
| 1 | Local rotation | `(a,b,c)=(c,a,b)` | 3,1,2 | 3,1,2 ✓ |
| 2 | Destructure + per-component implicit conv | `(uint256 x,uint256 y)=g()` where `g()->(uint8,uint8)=(255,7)` | 255,7 | 255,7 ✓ |
| 3 | Skipped component still evaluated + order | `(a,,c)=(se(1),se(2),se(3))` | a=1,c=3,log=123 | 1,3,123 ✓ |
| 4 | Nested destructure | `(a,(b,c))=(1,(2,3))` | 1,2,3 | 1,2,3 ✓ |
| 5 | Arity mismatch 2≠3 | `(uint a,uint b)=g()` (g→3) | REJECT (7364) | co-REJECT ✓ |
| 6 | Mixed decl+assign | `(uint a, b)=(1,2)` (b pre-declared) | REJECT (parser: expected identifier) | co-REJECT ✓ |
| 7a | `(x)` is `x` | `uint x=(5)` | ACCEPT | ACCEPT ✓ |
| 7b | `(x,)` 1-tuple | `uint x=(5,)` | REJECT ("Tuple component cannot be empty") | co-REJECT ✓ |
| 9 | Tuple LHS, pure/param/storage index | `(xs[i],ys[i])=(3,4)` | 34 | 34 ✓ |
| 9 | Tuple const idx, side-effecting RHS | `(xs[0],ys[1])=(rhs(3),rhs(4))` | 34 | 34 ✓ |
| 11 | Discard all returns (bare call stmt) | `g();` where g returns 2 | s=7 | 7 ✓ |

Notes:
- #6 mixed decl+assign is a solc **parser** error (`(uint a, b)` — the second
  component lacks a type in a declaration statement); co-rejected. solc does not
  permit mixing a new declaration and an existing lvalue in one tuple.
- The swap/rotation confirm solidity-lean evaluates the **whole RHS before any
  LHS write** (`Stmt.assignTuple` in `Interpreter.lean:8115` uses
  `evalTupleComponentsRefPreserving` then `writeTupleWithRuntime`), matching solc.
- #3 confirms skipped (`hole`) components' RHS side effects still fire, in
  left-to-right order.

## Summary

- **1 divergence (over-reject, ~99%):** tuple-assignment LHS component whose
  array/mapping index is an internal function call (`(a[f()], b) = …`). solc
  accepts and runs; solidity-lean fails at Executable lowering. Root cause:
  `SolidCore/Solidity/Interface.lean` `toCoreLValueTargets?` / `toCoreLValue?`
  lower the index with pure `Expr.toCore?` (no internal-call hoisting), and
  `Stmt.toCoreWithInternalCalls?` has no LHS-index-hoisting arm for the tuple
  path (MI1 covered only single-assign + return positions).
- Everything else probed (swap/rotation RHS-before-LHS, multi-return
  destructure + per-component conversion, skipped-component side effects &
  order, nested destructure, arity/mixed-decl/1-tuple rejects, discard-all) is a
  **clean match**.
