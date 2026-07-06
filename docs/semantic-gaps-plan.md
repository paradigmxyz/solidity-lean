# Plan: closing correctness/completeness gaps in the Solidity source semantics

**Status:** finalized (decisions recorded below). Scope is the three
known-deferred registry gaps; soundness-first; a separate worktree off current
HEAD; A1 gets a full rational-folding engine.

## Decisions (2026-07-06)

- **Scope:** the **known-deferred registry gaps only** (A1 rational constants,
  A2 balance accounting, A3 `gasleft`). No broad discovery/feature-coverage pass
  this round — sections B/C below are retained only as a future backlog, not
  active work.
- **Priority:** **soundness-first** → A1 leads (it is the one suspected of
  producing *wrong answers* on legal programs).
- **Worktree base:** a **separate git worktree off current HEAD**, starting now.
- **A1 fix shape:** a **full rational-folding engine** matching solc's
  unbounded-precision rational constant semantics (audit solc's exact behavior
  first to spec the engine, then build it — not a narrow scientific-notation
  patch).
- **Phase 5 coordination (consequence of the above):** A1 lives in
  elaboration/constant-folding (`Interface.lean` `inlineConstants` /
  `CoreExpr.evalWord?` / the solc-AST importer's literal path), **not** the
  evaluator — so it is conflict-free with the in-flight Phase 5 rewrite and is
  the correct first item off HEAD. A2/A3 touch the world environment / resource
  arm that Phase 5 is rewriting, so they **wait until Phase 5 merges** (starting
  them off HEAD now would guarantee a painful merge). Sequencing: **A1 now; A2/A3
  after Phase 5.**

## Purpose

A workstream **separate from the Phase 5 external-world refactor**: make the
executable Solidity *source-language* semantics agree with pinned solc 0.8.35 /
Forge on legal programs it currently mis-evaluates or over-rejects, and record
(not silently omit) what stays out of scope. This is *not* lowering and *not*
new external-world plumbing — it is language-fidelity of the interpreter/checker
itself.

**Verification stays the differential corpus.** Every gap is closed the roadmap
way: **pin a paired Forge/solc lane that exhibits the divergence first, confirm
red, then fix to green.** No fix without a lane. (This deliberately *adds* corpus
lanes — the freeze in Phase 6 is about not extending *coverage for its own sake*;
pinning a discovered bug is explicitly allowed.)

## Coordination with Phase 5 (important)

Several gaps live in exactly the interpreter code Phase 5 is rewriting
(`Interpreter.lean`: the evaluator, the world/`Context` fields, `gasleft`). Doing
both at once in one tree = merge pain. This work is planned for a **separate git
worktree**; the open question is what it **branches from** (see interview Q2):
- Gaps entangled with Phase 5: **intra-frame balance accounting** (the roadmap
  says "Phase 5's world environment creates the natural home for the fix"),
  **`gasleft` as `Query.resource`** (the alphabet arm exists but wiring is
  post-Phase-5), and anything touching the evaluator's external boundary.
- Gaps largely independent of Phase 5 (elaboration/typecheck/ABI/arithmetic):
  **rational constant folding**, **fixed-point arithmetic**, **type-conversion
  edge cases**, **ABI encode/decode edge cases**. These can proceed off current
  HEAD with low conflict risk.

## Gap inventory

Grouped by kind. Severity lens: **soundness** (mis-evaluates a legal program →
wrong answer) > **fidelity** (diverges from solc on an edge case) >
**completeness** (rejects a legal program) > **out-of-scope** (recorded, not
fixed).

### A. Known-deferred, from the roadmap gap registry

| # | Gap | Kind | Notes |
|---|-----|------|-------|
| A1 | **Rational constant expressions** | **soundness (suspected)** | solc folds constants in unbounded-precision rationals (`1e18`, fractional/sub-denominated intermediates, huge powers that cancel). No rational-folding machinery here; one importer path requires plain decimal naturals. **May currently mis-evaluate or silently reject legal programs.** Audit-first: measure the blast radius before choosing a fix. |
| A2 | **Intra-frame balance accounting** | soundness / fidelity | `msg.value` never credits the callee; `address(this).balance` and value sends read/write nothing. Real EVM credits before body execution — Solidity-observable. Entangled with Phase 5's world environment. |
| A3 | **`gasleft` as resource query** | fidelity | Today a fixed ambient word. Becomes `Query.resource gas`. Entangled with Phase 5; exact gas alignment with Yul is separately deferred. |

### B. Fidelity areas — FUTURE BACKLOG (out of this round's scope per decision)

Not active work this round (scope = known-deferred gaps only). Retained as a
backlog so the thinking isn't lost; each would need a differential probe to
confirm before becoming a work item.

| # | Area | Why suspect |
|---|------|-------------|
| B1 | **Subexpression / argument evaluation order** | Already modeled as Solidity's *unspecified* order (checker accepts any consistent child-eval order via `withUnspecifiedChildEvalOrders`). Likely *sound*, but worth a targeted probe on side-effecting args / tuple assignments / `a[i] = f()` to confirm we accept exactly what solc accepts (neither more nor less). |
| B2 | **Fixed-point arithmetic (`fixed`/`ufixed`)** | The type surface models `fixed`/`ufixed` (Ast.lean), but solc 0.8.x only *partially* supports fixed-point (most operations are disallowed). Confirm we reject exactly what solc rejects and compute exactly what it computes — over-permissive fixed-point would be unsound. |
| B3 | **Integer arithmetic edges** | checked/unchecked over/underflow, `type(intN).min` division, shift by ≥ width, exponentiation, signed mod/`%` sign rules, narrowing conversions. Corpus covers common cases; audit the boundary values. |
| B4 | **Type conversions** | address↔uint160, contract↔address, bytesN↔uintN↔intN width/padding rules, enum range, literal→type implicit-conversion rules, `bytes`↔`string`. Rich rule surface; a known divergence magnet. |
| B5 | **ABI encode/decode edge cases** | `abi.encodePacked` ambiguity, dynamic nested types, `abi.decode` strictness, empty/oversized calldata, non-canonical bool/address inputs. Corpus has `abi-*` cases but not exhaustive. |
| B6 | **Storage packing / layout edges** | multi-var slot packing, struct/array-in-struct, mapping-in-struct, `bytes`/`string` short vs long form, `delete` on nested aggregates. Spec-defined (in scope), edge-heavy. |
| B7 | **Event / error encoding** | indexed dynamic topics (keccak of value), anonymous events, custom-error selectors, `Panic(uint256)` codes. |

### C. Completeness — FUTURE BACKLOG (out of this round's scope per decision)

The solc-AST importer is fail-closed with zero unimplemented node types *over the
current corpus*, but that is corpus-relative. A **feature-coverage audit** against
the Solidity 0.8.35 grammar will surface constructs no corpus case exercises
(e.g., `unchecked` nesting, `using … for` with operators, transient storage
`tstore`/`tload` surface, `try/catch` with multiple typed catch clauses,
free functions, user-defined value types with operators, `constant`/`immutable`
edge cases). Each: confirm it's a deliberate exclusion or a gap to close.

### D. Out of scope by design (recorded, NOT in this plan)

Inline assembly; imports / multi-file units; closed-world multi-contract
execution; gas metering; create `initCode` as real compiled bytecode. These stay
in the roadmap's gap registry as recorded exclusions.

## Discovery method (for unknown gaps)

Two complementary passes, both cheap given the harness already exists:
1. **Differential probing** — small hand-written `.sol` fixtures targeting each
   B/C area, run through the existing paired harness (pinned solc + Forge vs. the
   Lean interpreter). A divergence = a confirmed gap + its pinning lane, for
   free. Optionally lightweight fuzzing (random small expressions over the B3/B4
   surface) to catch the unexpected.
2. **Feature-coverage audit** — enumerate the Solidity 0.8.35 grammar /
   language-feature checklist, mark each construct as {covered green / covered
   red / not exercised / excluded}, to convert "unknown unknowns" into a
   tracked list.

## Per-gap workflow (the discipline)

1. **Probe** → a minimal paired fixture that diverges (or confirms parity).
2. If it diverges: **pin** it as a new corpus lane (red), classify severity.
3. **Fix** the interpreter/checker minimally; lane goes green; full corpus stays
   green.
4. **Record** in `docs/DECISIONS.md` (and update the roadmap gap registry:
   move fixed items out, keep genuine exclusions).
5. Soundness gaps (A1, over-permissive B2/B3/B4) take priority over completeness.

## Sequencing (finalized)

1. **A1 — rational-folding engine** (now, off HEAD, conflict-free):
   1. **Audit solc's exact rational semantics** with probe fixtures: `1e18` and
      other scientific notation; sub-denominations (`wei`/`gwei`/`ether`,
      `seconds`/`minutes`/…); fractional intermediates that resolve to integers
      (`(1 ether) / 3 * 3`, `7 / 2 * 2`); huge powers that cancel (`2**256 / 2**255`);
      mixed rational/integer const exprs; and the *rejection* boundary (a rational
      that doesn't resolve to the target integer type → solc error). Capture each
      as a paired Forge/solc lane and note where our interpreter currently
      diverges (wrong value) or over-rejects (rejects a legal program).
   2. **Design + build the engine**: represent constant expressions as
      unbounded-precision rationals (`ℚ` — numerator/denominator over `Int`)
      through folding, matching solc: exact arithmetic on `+ - * / ** << >>` and
      unary, sub-denomination scaling, then a single final check that the folded
      rational lands exactly on the target type's integer (else the same error
      solc raises). Replace the current "plain decimal naturals" importer path
      and any lossy fold with this. Keep it total (no `partial`).
   3. **Pin + fix + green**: each probe lane goes green; full corpus stays green;
      record in `docs/DECISIONS.md` and move A1 out of the roadmap gap registry.
2. **A2 balance / A3 gasleft** — **after Phase 5 merges** (entangled with the
   world environment / `Query.resource` arm; starting them off HEAD now would
   conflict with the in-flight evaluator rewrite).

## Execution note

A1 runs in a **separate git worktree off current HEAD** (branch e.g.
`gaps/rational-constants`) so it proceeds in parallel with Phase 5 without
touching the same files. Its differential lanes are new corpus cases (allowed —
pinning a discovered bug). It merges back after Phase 5, or independently if it
lands first (low conflict — different files).
