# R1: Intrinsic evaluation order — design note

Goal: delete the threaded `ChildEvalOrder` machinery and bake each construct's
sibling-evaluation order into its evaluator arm, matching solc 0.8.35 legacy
codegen (`libsolidity/codegen/ExpressionCompiler.cpp`).

## Machinery being deleted
- `inductive ChildEvalOrder` (Interpreter.lean:1736)
- `Context.childEvalOrder?` field (1768) + init in `Context.empty` (1793)
- `Context.withChildEvalOrder` / `withoutChildEvalOrder` (7422/7426)
- `ChildEvalOrder.yulCompatible` (7434), `Context.effectiveChildEvalOrder` (7437)
- the `order : ChildEvalOrder` parameter threaded through the whole
  expression-eval family (renamed, order param dropped):

| old name | new name |
|---|---|
| `Expr.evalWithRuntimeOrderFuel` | `Expr.evalFuel` |
| `Expr.evalListWithRuntimeOrderFuel` | `Expr.evalListFuel` |
| `Expr.memoryRefOrValueWithRuntimeOrderFuel` | `Expr.memoryRefOrValueFuel` |
| `Expr.resolveLValueWithRuntimeOrderFuel` | `Expr.resolveLValueFuel` |
| `Expr.evalWithRuntimeOrder` | `Expr.eval` |
| `Expr.evalListWithRuntimeOrder` | `Expr.evalList` |
| `Expr.memoryRefOrValueWithRuntimeOrder` | `Expr.memoryRefOrValue` |
| `Expr.evalMemoryRefPreservingWithRuntimeOrder` | `Expr.evalMemoryRefPreserving` |
| `Expr.resolveLValueWithRuntimeOrder` | `Expr.resolveLValue` |
| `Expr.evalTupleComponentsRefPreserving(Fuel)` | same name, order param dropped |
| `Expr.evalBinaryWithRuntimeOrder` | `Expr.evalBinary` |
| `Expr.evalReturnValueWithRuntimeOrder` | `Expr.evalReturnValue` |
| `Expr.evalReturnListWithRuntimeOrder(Fuel)` | `Expr.evalReturnList(Fuel)` |
| `Expr.evalRefArgWithRuntimeOrder` | `Expr.evalRefArg` |
| `Expr.evalRefArgListWithRuntimeOrder(Fuel)` | `Expr.evalRefArgList(Fuel)` |

Name-collision check: none of the new names exist anywhere in the repo
(grepped `def Expr.eval `, `Expr.evalList\b`, etc. — no hits outside the family).

## `match order` / `match context.effectiveChildEvalOrder` sites and the chosen intrinsic branch

Expression family (Interpreter.lean, mutual block 6342–7310 + list evaluators):

| line | construct | intrinsic order | branch kept | solc ref |
|---|---|---|---|---|
| 6536 | `Expr.assignExpr` (RHS vs LHS-ref) | RHS then LHS-ref | rightToLeft | 319,331 (PRESERVE) |
| 6557 | `Expr.assignOpExpr` | RHS then LHS-ref | rightToLeft | 336-370 (PRESERVE) |
| 6581 | `Expr.assignOpCleanupExpr` | RHS then LHS-ref | rightToLeft | 336-370 (PRESERVE) |
| 6637 | `Expr.binary` (non-short-circuit) | RIGHT then LEFT | rightToLeft | 614-615 (PRESERVE) |
| 7151 | `Expr.evalListFuel` (all arg/tuple/array/abi/index-pair lists) | LEFT to RIGHT | leftToRight | 710-711,682-684,1031,400,388 (CHANGE) |
| 7208 | `Expr.memoryRefOrValueFuel` index base-vs-key | base then key (L2R) | leftToRight | IndexAccess visitor (CHANGE) |
| 7291 | `Expr.resolveLValueFuel` index base-vs-key | base then key (L2R) | leftToRight | IndexAccess visitor (CHANGE) |
| 7394 | `Expr.evalTupleComponentsRefPreservingFuel` | LEFT to RIGHT | leftToRight | 400 (CHANGE) |
| 7504 | `Expr.evalReturnListFuel` | LEFT to RIGHT | leftToRight | TupleExpression (CHANGE) |
| 7571 | `Expr.evalRefArgListFuel` (internal-call args) | LEFT to RIGHT | leftToRight | 710-711 (CHANGE) |

Statement level (`Stmt.eval`):

| line | construct | intrinsic order | branch kept |
|---|---|---|---|
| 8449/8453 | `Stmt.assign` target-vs-RHS | RHS then target | evalRhsThenTarget (PRESERVE) |
| 8526 | `Stmt.assignOp` | RHS then target | evalRhsThenTarget (PRESERVE) |
| 8566 | `Stmt.assignOpCleanup` | RHS then target | evalRhsThenTarget (PRESERVE) |

All other consumers of `effectiveChildEvalOrder` (~80 sites, lines 7457–9383)
are plain pass-throughs into the family above; the arg is simply removed.
Notable ones that become L2R by inheriting the new `evalListFuel`:
- `Stmt.revert name exprs` (9268) — custom-error args (solc 9268 / Kind::Error
  ABI-encodes L2R)
- `Stmt.returnValues` (9246) — return tuple L2R
- `Expr.abiEncode*`/`Expr.tuple`/`Expr.fixedArray`/`concatBytes`/
  `addMod`/`mulMod`/`fixedBytesIndex [base,idx]`/`slice [base,start,stop]`
  (6656–7139) — all via `evalListFuel`, L2R
- internal/external call args (8629–8943 region + 7067/7080 index pair) — L2R
- Short-circuit `&&`/`||` (6611/6623): already left-first with guarded right —
  untouched.

## `Stmt.emitEvent` — bespoke TWO-PHASE evaluator (line 9273)
solc (ExpressionCompiler.cpp Kind::Event, 976–1043): indexed (topic) args are
evaluated in REVERSE source order first (`for (arg = size; arg > 0; --arg) if
indexed`), then non-indexed (data) args in FORWARD source order (`for (arg = 0;
arg < size; ++arg) if !indexed`).

Indexed-flag availability: `context.eventDecl? name : Option EventDecl`;
`EventDecl.fields : List EventField` with per-position `indexed : Bool`
(populated positionally by the importer, Interface.lean:22668-22677). Legacy
hand-built decls may have `fields = []` and use `indexedCount` with the
convention "first indexedCount args are the indexed ones"
(`Runtime.emitEvent`, 7869-7873) — flags fall back to
`i < decl.indexedCount` in that case. No decl → all-false (plain L2R; the
subsequent `Runtime.emitEvent` errors anyway).

Implementation: build the evaluation schedule
`(indexed positions).reverse ++ (data positions)`, evaluate the scheduled
exprs with the (now L2R) `Expr.evalList`, then reassemble VALUES into
positional order before calling `Runtime.emitEvent` (which encodes
positionally). All-non-indexed events degenerate to plain L2R (identical
schedule), anonymous/all-indexed likewise consistent.

## Witness / proof references to fix
- `SolidCore/Witness/GasleftResource.lean:34-35` — passes
  `ChildEvalOrder.leftToRight` to `evalWithRuntimeOrderFuel 4`; becomes
  `Expr.evalFuel 4`. (This one IS `#eval`-enforced.)
- `SolidCore/Witness/Interface.lean` 20840–21320 — five order-parametric
  families (`unspecifiedBinaryOrder*`, `unspecifiedTupleOrder*` expr+stmt,
  `unspecifiedLValueIndexOrder*`, `unspecifiedStatementAssignOrder*`,
  `unspecifiedMemoryRefOrder*`): drop the `order` parameter, delete the
  LeftToRight/RightToLeft directional `Matches` pairs, keep one combined
  `...Matches` def pinning the NEW intrinsic expectation. Unenforced
  (typecheck-only), but expectations updated for truthfulness:
  - binary `(x=5) + x` → value 5·2? NO: R-then-L pinned: rhs `x`=0 read first?
    rhs is `x` (reads 0), then lhs `(x=5)`=5 → value 5+0=5? Careful: value =
    lhs+rhs = 5+0 = 5, slot=5. (unchanged from old R2L pin)
  - tuple `((x=5), x)` → L2R now: first=5, second=5, slot=5 (CHANGED pin)
  - lvalue index `matrix[x=1][x] = 9` → base-then-key: writes [1][1]:
    first=m[1][0]=0, second=m[1][1]=9, seen=1 (CHANGED pin)
  - stmt assign `xs[i] = (i=1)` → RHS-then-target: xs[1]=1: first=0, second=1,
    seen=1 (unchanged pin)
  - memoryRef `alias = matrix[(x=1)][x]` → base-then-key → alias=m[1][1]:
    first=0, second=7, seen=1 (CHANGED pin)
- `SolidCore/Witness/Checked.lean` 3482–3735 — five
  `checkedUnspecified*WithContextEval (order)` families using
  `withChildEvalOrder`: same treatment (drop param, pin new expectations).
  Also `checkedUnspecifiedTupleOrderDeterministicRunMatches` (~3455) pins OLD
  tuple R2L (second=0) → update to second=5.
- `SolidCore/Witness/InternalCall.lean:191` — comment naming
  `evalRefArgWithRuntimeOrder` → rename mention.
- `SolidCore/Solidity/FuelMonotonicity.lean` — statements are about
  `Stmt.eval*` fuel only; expression eval has its own fuel (comment at :36).
  The emitEvent arm body changes shape (no stmt-fuel use added), so the
  Stmt.eval induction should replay; adjust the emit case if the proof
  pattern-matches the arm.

## Verification plan
- New `SolidCore/Witness/EvalOrderIntrinsic.lean` (#eval-enforced) pinning:
  tuple-RHS, return-tuple, emit all-data, emit mixed indexed/data two-phase,
  custom-error args, abi.encode args, m[i++][i++]=99, nested index read,
  internal-call args L2R, binary R-then-L control, arr[i++]=i++ control,
  compound-assign control, short-circuit controls.
- New Forge lane fixture(s) with the same constructs incl. a mixed
  indexed/non-indexed event with side-effecting args; ground truth via forge.
- `--only` replay on frontend-frontier, openzeppelin-erc20-capped-pausable,
  calldata-ref-internal + event/tuple fixtures.

## Addendum (discovered during verification): binary-with-CALLS order lives in the IMPORTER hoisters
The interpreter's binary arm only orders the RESIDUAL operands; calls in
operands are hoisted into prefix statements by the enumerated call-position
hoisters in `SolidCore/Solidity/Interface.lean`, whose emission order decides
the observable order. The general ANF fallback (`Expr.anfHoist`, 13325-13351)
was ALREADY right-then-left for ordinary binaries, but the enumerated
`internalBinarySingleReturnUseCore?` / `externalBinarySingleReturnUseCore?`
paths were LEFT-call-first (live bugs #187/#191). Fixed to right-first
(ground truth: Forge `rd() + wr() == 5`, ExpressionCompiler.cpp:606-616 —
the only swap is the literal-reorder optimization, side-effect-free):
  * both-internal-calls path: RHS call parked in `_sol_bin_rhs`, LHS call second;
  * `internalTwoSingleReturnCallsRightFirstCore?` — NEW right-first twin used
    ONLY by the binary fallback (the original left-to-right helper still serves
    require/emit/revert two-arg forms, which are argument positions);
  * lhs-call + pure-rhs (internal and external): RHS value parked in a temp
    BEFORE the call when the RHS type resolves (else previous shape kept);
  * pure-lhs + rhs-call (internal and external), ordinary ops: the call runs
    first and the pure LHS stays in the residual binary (runtime arm is
    right-then-left) — the old `_sol_bin_lhs` pre-binding is now
    short-circuit-only.
  * both-non-core operands (each carrying a nested call — e.g. ternary-wrapped
    calls on both sides, `internalBinarySingleReturnUseCore?` `none,none` /
    `_, none` sub-case): fixed to right-first — the RHS value is parked in a
    `_sol_bin_<tag>_rhs` temp, the LHS runs second, and the residual binary is
    left for the right-then-left runtime arm. Falls back to the prior left-first
    shape only when the RHS type is unresolvable (never trades a lowerable
    statement for `none`). Regression: `Witness/BinaryTernaryOperandOrder.lean`.
Short-circuit `&&`/`||` paths are untouched (left-first, guarded right).
