# LOWERING_UNIFY_DESIGN — WS1: finish the lowering unification

Branch `rearch/lowering-unify`, base `6c431c0` (WS2 value-typing + WS3 calldata
tail-wrap on main). Successor to `ENV_LOWERING_DESIGN.md` (R2): this workstream
retires the R2 Stage-D residual debt — the remaining env-LESS PRIMARY lowering
positions, the `Stmt.toCoreWithInternalCalls?` enumerated dispatch, and the
hoister order/gensym seams.

## 1. The env-less-shadow map (state at base, before this branch)

Two parallel lowerings still coexist in `SolidCore/Solidity/Interface.lean`:

- env-aware: `Expr.toCoreAsWithEnvFuel?` (one fuelled recursion since R2
  Stage B) + statement-side helpers `assignmentCoreWithEnv?`,
  `varDeclCoreWithEnv?`, `Expr.toCoreLValueWithEnv?`,
  `Expr.conditionCoreWithEnv?`, `Args.toAbiEncodeSourceWithEnv?`.
- env-less shadow: `Expr.toCore?` / `Expr.toCoreAs?` / `Expr.toCoreLValue?` /
  `Args.toCoreExprs?` / `Stmt.toCore?`.

A position is a BUG exactly when the env-less path is PRIMARY for a value that
can carry narrow (`uintN/intN`, N<256) checked arithmetic: the operand-width
cleanup (`uintCleanup`/`intCleanup` → Panic 0x11) is skipped, and inside
`unchecked` the wrap width is wrong (wrong VALUE).

Enumerated PRIMARY env-less positions at base (the audit target):

| # | position | status |
|---|----------|--------|
| A | assignment RHS member-call builtin (`z = abi.encode(a+b)`) | #201 patch |
| B | vardecl init builtin/hash (`bytes memory z = abi.encode(a+b)`, `bytes32 h = keccak256(...)`, incl. list-form arm + cast-of-builtin `uint256(keccak256(...))`) | #201 patch |
| C | `.length`-of-builtin in conditions (`require(abi.encode(a+b).length > 0)`) | #201 patch |
| D | emit args: builtin arg, pure narrow arg beside a call arg, call-free catch-all | #201 patch |
| E | revert custom-error args (call-free catch-all) | #201 patch |
| F | nested builtin-in-builtin (flag stopped at one level) | #201 patch |
| G | compound-assign / delete lvalue index keys (`arr[a+b] += 1`, `delete arr[a+b]`) | #201 patch |
| H | anything ELSE the probe battery (§3) finds | THIS BRANCH |

Legitimately env-less (kept, justified in ENV_LOWERING_DESIGN §"Remaining
legitimate env-less callers"): the leaf workhorse under
`toCoreAsWithEnvDirect?`/`coreAsFromTy?` (type applied at the boundary),
literal-only constant folds (MUST stay compile-time folds — the uniswap-v2
`2**112` regression), importer/getter-synthesized expressions, and every
`| none => Stmt.toCore? ...` acceptance-preserving FALLBACK (reached only when
the env-aware path declines, i.e. behavior-neutral for accepted programs
where the env path succeeds).

## 2. Measured proof-risk surface (BEFORE editing)

- `SolidCore/Solidity/FuelMonotonicity.lean`: **0** references to
  `toCore?`/`toCoreWithInternalCalls?`/`toCoreAsWithEnv*`/`assignmentCoreWithEnv?`/
  `varDeclCoreWithEnv?` (it pins `Stmt.eval*` fuel only).
- `SolidCore/Solidity/AdoptionLaws.lean`: **0** references to the lowering
  family.

So the lowering changes carry NO expected proof churn; the gate is the full
`lake build` (witness `#guard`s re-execute the emitted core through the
interpreter). Witnesses that inspect emitted core are cleanup-tolerant by
convention (recurse through `uintCleanup`).

## 3. Stage plan

### Stage 1 — env-audit fixes
Fold in the ready, EVM-verified #201 precursor (identical to the
`fix-wt-bytesneq` dev worktree diff): flag deepening
(`Expr.abiArgNeedsEnvCleanupFuel?`, budget 8), cast-of-builtin and
`.length`-of-builtin arms in `Expr.toCoreAsWithEnvFuel?`, new helpers
`Expr.abiArgCoreWithEnvCleanup?` / `Args.toCoreExprsWithEnvCleanup?`, and the
dispatcher reroutes for A–G. Ship its 30-pin witness
(`SolidCore/Witness/LoweringUnify.lean`) + Forge lane
`tests/forge-harness/builtin-arg-residue` (29 real-EVM tests, all PASS on
pinned solc 0.8.35).

Then the SYSTEMATIC audit (§H): one batch probe contract covering every
remaining statement/expression position that can carry narrow checked
arithmetic — named event/error args, array literals, struct ctor args
(positional + named), `new T[](a+b)` sizes, tuple assign/decl RHS, external
call args, try-call args, modifier args, library/fn-pointer internal call
args, `addmod`/`mulmod` args, storage `push(a+b)`, nested index keys, for-init
vardecl, indexed event args, delete-of-mapping keys, unchecked wrap-width
controls. Model verdicts vs real-EVM (Forge) ground truth; every divergent
position gets the same treatment as A–G: reroute through the EXISTING
env-aware helper, gated so unflagged shapes stay byte-identical.

### Stage 2 — hoister order-faithfulness + #196
- #196 NESTED-LIBRARY-CALL-TEMP-SHADOW: `internalCallArgTempName` produces
  `_sol_internal_call_arg_eval0` at EVERY recursion depth of
  `FunctionDecl.internalSingleReturnCallExprCore?` (self-recursion at
  ~14514) and `internalTypeConversionSingleReturnUseCore?` (~14917). The
  inner `Stmt.varDecl` re-declares the SAME name inside the inner block, so
  the inner `assign` writes the shadow and the outer temp keeps its default
  → chains ≥3 deep (`f(g(h(x)))`) compute garbage. Fix: thread a `depth : Nat`
  parameter through `internalSingleReturnCallExprCore?`; the hoist prefix
  becomes depth-suffixed (`_sol_internal_call_arg_d<k>` for k>0), leaving
  every depth-0 emission (all currently-working shapes) byte-identical.
- Order audit: verify (Forge ground truth) the hoisters preserve intrinsic
  order for: call args L2R, two-phase emit (indexed args REVERSE order first,
  then data forward — probe `emit E2I(bump(), bump())` with BOTH args
  indexed), array/tuple element hoists, index base-then-key. Binary
  right-then-left was fixed in R1 (#187/#191); untouched here.

### Stage 3 — the `Stmt.toCoreWithInternalCalls?` dispatch collapse
Measured shape of the dispatcher (base): 2,570 lines, 89 merged arms /
117 top-level `| Stmt.*` patterns; exactly ONE arm is a literal re-dispatch
(`| other => Stmt.toCore? storageNames other` — the default), while 155
`Stmt.toCore?` occurrences are `| none =>` FALLBACKS inside arms that do
genuine work first (internal-call hoisting, storage-alias returns, two-phase
emit, external-call binding). Plan: collapse what is safely collapsible —
route the DEFAULT arm's env-relevant statements through env-aware helpers
(largely achieved by the #201 catch-all emit/revert arms) and delete
`Stmt.toCore?` arms that become unreachable; KEEP the acceptance-preserving
fallbacks (removing them flips accepted programs to rejects, which the frozen
replay corpus forbids). If full deletion of the `Stmt.toCore?` shadow proves
entangled (it is also the recursion workhorse for `Stmt.block`/loop BODIES
inside itself), stop and record the exact residue.

### Opportunistic
Factor the verbatim-duplicated depth-2 `address(T(inner))` conversion arm
(nonpayable + payable copies in the env-less pass) into one helper.

## 3b. Stage-1 audit RESULTS (probe battery, real-EVM ground truth)

32-probe battery (`tests/forge-harness/lowering-unify-audit`, all 32 PASS on
pinned solc 0.8.35 via Forge). Model verdicts before/after the Stage-1b fixes:

| probe | real EVM | model BEFORE | model AFTER | fix |
|---|---|---|---|---|
| `new uint256[](a+b)` size | Panic 0x11 | **RET 300** | Panic 0x11 | env `newExpr` arm + vardecl/return reroutes |
| `this.sink(a+b)` ext-call arg | Panic 0x11 | **decode-revert (other)** | Panic 0x11 | `argEnvLower` threading |
| `try this.sink(a+b)` | Panic 0x11 (uncaught) | **RET 99 (caught!)** | Panic 0x11 | same (calldata-eval failure already bypasses catch) |
| `addmod(a+b,1,7)` | Panic 0x11 | **RET 0** (=(300+1)%7) | Panic 0x11 | env addmod/mulmod arm + flag |
| `arr[arr[a+b]]` | Panic 0x11 | **Panic 0x32 (OOB)** | Panic 0x11 | index-flag recursion + wide-key gate |
| `uint8[2] memory t=[a+b,1]` | Panic 0x11 / 7 safe | **OVER-REJECT** (whole contract failed to lower) | Panic 0x11 / 7 | env `Expr.array` arm + `Exprs.toCoreAsListWithEnvFuel?` |

GREEN from the start (controls, all confirmed): named emit/revert args,
struct ctor (positional+named), tuple assign/decl, lib/fn-ptr/modifier args,
`addmod` safe, `push(a+b)`, for-init vardecl, `delete m8[a+b]`, indexed emit,
unchecked wrap-width (44), two-phase indexed emit `E2I(bump(),bump())`
(topics x=2,y=1 — the #195 schedule hoister is order-faithful).

**#196 status:** chain3/chain4/chain3lib/chain3vd/chain3emit (internal AND
library 3-4-deep nested call chains, return/vardecl/emit positions) all
return CORRECT values (27/32/27/27/topic-27) even BEFORE the gensym fix —
those shapes now lower through the boundary-call path
(`internalCallParts?`), not the colliding hoister. The collision in
`FunctionDecl.internalSingleReturnCallExprCore?` (+ its
`internalTypeConversionSingleReturnUseCore?` twin) is nevertheless
structurally present whenever `Args.replaceInternalSingleReturnCallExprArg?`
fires at two nesting levels; fixed by the depth-suffixed temp prefix
(`_sol_internal_call_arg` at depth 0 — byte-identical for every
currently-emitting shape — `_sol_internal_call_arg_d<k>` below). No
reproducing divergence was found post-boundary-rearch; the fix removes the
latent seam.

## 3c. Stage-3 assessment (dispatch collapse)

Measured on this base: the `Stmt.toCoreWithInternalCalls?` dispatcher is
2,570 lines / 89 merged arms, and exactly ONE arm is a literal re-dispatch —
the default `| other => Stmt.toCore? storageNames other`. The other 155
`Stmt.toCore?` occurrences are `| none =>` ACCEPTANCE-PRESERVING FALLBACKS
inside arms that first do genuine work (call hoisting, storage-alias
returns, two-phase emit, external-call binding, env-aware reroutes).
Deleting the `Stmt.toCore?` shadow would flip accepted programs to rejects
wherever an env-aware path legitimately declines (storage-name-only
contexts, importer-synthesized bodies, getter generation — all call
`Stmt.toCore?` as their PRIMARY with no env available). The "50-arm
re-dispatch collapse" premise no longer holds after R2 Stage C/D + #201 +
this branch: the dispatcher is already "env-aware/hoisting primary +
env-less fallback" arm by arm, and the 32-probe battery finds no remaining
statement position whose PRIMARY leaks width-cleanup. Stage 3 therefore
lands as: (a) this documented measurement, (b) the audit closing the default
arm's env-relevant remainder (emit/revert catch-alls came with #201; newExpr
vardecl/return reroutes with Stage 1b), (c) the opportunistic
`address(T(inner))` nonpayable/payable dedup. A syntactic single-recursion
rewrite of the dispatcher is deliberately NOT attempted — blast radius
(~2,500 lines of load-bearing enumeration, zero failing probes to justify
it) far exceeds the gate budget; recorded as residual debt.

## 4. Gate
Full `lake build` green (incl. FuelMonotonicity, AdoptionLaws, all
witnesses); witness `SolidCore/Witness/LoweringUnify.lean` imported from
`SolidCore.lean`; Forge lane(s) + additive manifest entries; sequential
self-gate on the new lanes + lowering-heavy existing lanes
(openzeppelin-erc20, openzeppelin-access-control, reference-*, storage-*,
cond-narrow-cleanup, stage-d lanes). Full 262-case replay is the
orchestrator's (serialized, not run here).
