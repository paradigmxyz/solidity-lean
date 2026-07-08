# Plan for reviewing the remaining unexplored surfaces (solc-vs-Solidus divergence campaign)

**What this is.** A planning/meta doc that consolidates the still-unexplored
surfaces from every prior review round and lays out a prioritized, sequenced plan
for reviewing the rest. Solidus = our executable Lean 4 Solidity 0.8.35 semantics
(`SolidCore/Solidity/*.lean` + importer `scripts/solc_ast_to_lean_source.py`);
solc source of truth is READ-ONLY at `/Users/dan/Projects/solidity-src` (v0.8.35,
commit `47b9dedd`, the exact source of the pinned binary). This is **not** a review
— it does not fix or deeply probe; it organizes the remaining work so subsequent
rounds are targeted by the empirical pattern below.

---

## 0. The empirical pattern (drives all prioritization here)

Across ~9 review passes (`docs/solc-implementation-divergences{,-2..-7}.md`,
`docs/solc-source-coverage-review.md`, `docs/solidus-solc-deep-comparison.md`,
`docs/solc-memory-semantics-review.md`, `docs/solidity-feature-coverage.md`) a
sharp pattern held:

- **CLEAN (well-mined, zero wrong-VALUE bugs in 5 straight rounds):**
  arithmetic / cleanup / conversion helpers, the ABI encode+decode codec, and the
  ANALYSIS-PASS ACCEPTANCE rules
  (Type/TypeChecker/ViewPure/Override/ControlFlow/ContractLevel/PostType/
  Immutable/DeclarationType). Findings here were almost all accept/reject-boundary
  and mostly **importer-masked** (solc rejects → no AST → never differentially
  live).
- **BUG-RICH (where the real wrong-VALUE bugs hid):** value-producing CODEGEN and
  RUNTIME-BEHAVIOR surfaces where Solidus uses an **ABSTRACTION** or a
  **RE-DERIVATION** that must match solc's **CONCRETE** behavior. Every wrong-value
  bug of the campaign lives exactly there:
  - **V1** — calldata-slice OOB revert-data (Solidus re-derived the *revert
    encoding*: `Panic(0x32)` vs solc's empty `revert(0,0)`). *Fixed.*
  - **DL1** — storage/constructor order via DFS instead of reverse-C3 (Solidus
    re-derived the *layout ORDER* with its own traversal). *Open.*
  - **M1** — memory→memory ref assignment deep-copies instead of aliasing
    (Solidus's *id-keyed memory graph* mis-models the aliasing edge). *Open.*
  - **G1** — user-defined operators run as the built-in (importer dropped the
    resolved operator fn; interpreter re-derived the op on raw words). *Fixed.*
  - **S1/S3** — string-literal codepoints-not-UTF-8 / ternary packed width
    (value re-derivation). *Fixed.*

- **KEY HEURISTIC.** The highest-value remaining targets are surfaces where
  **(a)** Solidus uses an abstract model or re-derives a concrete solc behavior,
  **(b)** it is DIFFERENTIALLY-LIVE (solc compiles it → reachable in the harness),
  and **(c)** the frozen corpus is unlikely to have exercised the edge. Rank the
  **abstraction-vs-concrete** surfaces highest (that is exactly where V1/DL1/M1
  were). Deprioritize — but do not skip — importer-masked acceptance-only rules
  and already-well-mined value surfaces.

---

## 1. Coverage ledger

Status vocabulary: **WELL-MINED-CLEAN** (read line-by-line ≥1 round, no live
wrong-value found) · **PARTIALLY-REVIEWED** (some sub-surface read, named residue
remains) · **UNEXPLORED** (no round has read it on both sides) · **IN-FLIGHT-FIX**
(divergence found, fix not yet landed) · **OOS** (out of scope by decision).

| Surface | Status | Covered by |
|---|---|---|
| Arithmetic / cleanup / conversion helpers | WELL-MINED-CLEAN | div-1..5, source-coverage, deep-comparison |
| ABI encode+decode codec (scalars, head/tail, bounds, single/nested/dynamic-element fixed arrays) | WELL-MINED-CLEAN | div-1,-2,-5 (AD1 REFUTED), source-coverage |
| Analysis-pass acceptance (Type/ViewPure/Override/ControlFlow/ContractLevel/PostType/Immutable/DeclType) | WELL-MINED-CLEAN | div-2,-3,-4, deep-comparison G2–G16 |
| Value builtins: selector/topic0/error-selector, addmod/mulmod, concat, min/max, fn-ptr members | WELL-MINED-CLEAN | div-6 (F1–F5) |
| C3 dispatch / override winner / `super` chain | WELL-MINED-CLEAN | div-7 (F1–F3, sim-verified) |
| Modifier substitution / chaining / arg-timing / return-capture | WELL-MINED-CLEAN | div-7 (F4) |
| Fallback / receive dispatch precedence | WELL-MINED-CLEAN | div-7 (F5) |
| Mapping/array/bytes slot math + `delete` of complex storage | WELL-MINED-CLEAN | div-7 (F6) |
| String / unicode / hex literal VALUE (UTF-8 bytes, length, hash) | WELL-MINED-CLEAN | source-coverage S1 (fixed), deep-comparison |
| Memory model: alloc/zero-init, storage↔memory copy, calldata→memory, `.length`, delete-clear | WELL-MINED-CLEAN | memory-review |
| Calldata narrow-int/enum aggregate element cleanup (lazy-on-access) | WELL-MINED-CLEAN | deep-comparison (S2 read-to-bottom, faithful) |
| **Storage-slot layout ORDER + ctor/init order (non-trivial diamond)** | **IN-FLIGHT-FIX (DL1)** | div-7 |
| **Memory→memory ref alias for non-`var`/`index` RHS shapes** | **IN-FLIGHT-FIX (M1)** | memory-review |
| Transient-storage (`tstore`/`tload`) slot allocation ORDER (shares DL1's traversal) | UNEXPLORED | div-7 flags as inherited-from-DL1, not probed |
| Storage packing ACROSS the inheritance boundary, re-audited post-DL1 | PARTIALLY-REVIEWED | div-7 (packing cursor read faithful per-order; interaction with corrected order not re-audited) |
| Memory-ref aliasing ACROSS the internal-call boundary; tuple-destructure of multiple memory refs | PARTIALLY-REVIEWED | memory-review (same-root-cause as M1, not separately probed) |
| Low-level `call`/`staticcall`/`delegatecall` return + revert **bubbling** (returndata, nested revert, empty-vs-Error-vs-Panic propagation) | UNEXPLORED | none — lanes drive happy-path options only |
| `create`/`create2` + `selfdestruct` execution **observables** (address, balance movement, deploy-revert bubbling, code) | PARTIALLY-REVIEWED | feature-coverage: create/selfdestruct laned; edge observables + create2 address (G22) OOS/unexplored |
| Precompile INPUT framing beyond ecrecover/sha256/ripemd160 (modexp 0x05, ecadd/ecmul/pairing 0x06–08, blake2f 0x09, point-eval 0x0a) | UNEXPLORED | div-6,-7 flag; only Solidus's own calldata framing is the divergence surface (results responder-answered) |
| `abi.encodeCall` full argument-tuple TYPE-MATCH acceptance | PARTIALLY-REVIEWED | div-6,-7 (selector+arg-encoding faithful; arity/implicit-conversion acceptance not exhaustively traced) |
| ABI encoder deep edges: function-type element, tuples-in-tuples, deeply nested `T[][]`/`string[]` round-trips | PARTIALLY-REVIEWED | feature-coverage UNKNOWN #2,#3 |
| `abi.encodeWithSelector`/`encodeWithSignature` dynamic-arg edges | PARTIALLY-REVIEWED | feature-coverage UNKNOWN #3 |
| `blockhash`/`blobhash` availability-WINDOW semantics (out-of-range → 0) | PARTIALLY-REVIEWED | div-6; builtins now laned (values), window-bound acceptance not re-examined |
| Event/error encoding DEEP edges (indexed reference hashing corners, anonymous topic layout) | WELL-MINED-CLEAN (spot) | div-6 F1 (event-indexed-dynamic green); deep corners not adversarially isolated |
| Block/tx environment completeness | WELL-MINED-CLEAN | feature-coverage (full magic-member set) |
| `type(C).creationCode`/`runtimeCode` concrete BYTES | OOS (opaque bytes; only `.length`/hash observable) | div-6 |
| `using ... for *` wildcard value semantics (G20) | WELL-MINED-CLEAN | deep-comparison G20 (now laned) |
| G17–G19, G21 untested-but-modeled paths | WELL-MINED-CLEAN | deep-comparison (now pinned) |
| Inline assembly / Yul / imports / multi-file / real gas / create-initcode-bytecode | OOS | feature-coverage §10 |

---

## 2. Prioritized remaining-surface backlog

Scored by the heuristic. Columns: **Abs/Re-der** = uses an abstraction or
re-derives a concrete solc behavior · **Diff-live** = solc compiles it and it is
reachable in the harness · **Corpus-miss** = frozen corpus unlikely to exercise
the edge · **Sev** = expected severity if a bug exists (wrong-value >
wrong-order > wrong-accept/reject > completeness). Abstraction-vs-concrete
surfaces are at the top — that is where V1/DL1/M1 were.

| # | Surface | Abs/Re-der | Diff-live | Corpus-miss | Sev | Prio |
|---|---|---|---|---|---|---|
| 1 | **DL1 storage/ctor order (land the fix)** | Y (layout order re-derivation) | Y | Y | wrong-value + wrong-order | **P0** |
| 2 | **M1 memory alias family (land the fix)** | Y (id-keyed memory graph) | Y | Y | wrong-value (wrong-alias) | **P0** |
| 3 | **Low-level call/staticcall/delegatecall return + revert bubbling** | Y (open-world responder re-derives returndata + revert propagation) | Y | Y (lanes drive happy path) | wrong-value (returndata / bubbled revert) | **P0** |
| 4 | **Transient-storage slot allocation ORDER** | Y (shares DL1's DFS traversal) | Y (transient laned) | Y (diamond+transient absent) | wrong-order → wrong-value | **P0** |
| 5 | **create/create2 + selfdestruct execution observables** | Y (open-world/postWorld re-frames address, balance, deploy-revert) | partly | Y | wrong-value (address/balance/bubbled deploy-revert) | **P1** |
| 6 | **Memory-ref aliasing across the internal-call boundary; tuple-destructure of memory refs** | Y (same graph as M1) | Y | Y | wrong-value (wrong-alias) | **P1** (rides M1 fix) |
| 7 | **Storage packing across inheritance re-audited post-DL1** | Y (packing cursor × corrected order) | Y | Y | wrong-value (slot) | **P1** (rides DL1 fix) |
| 8 | **Precompile INPUT framing (modexp/ecadd/ecmul/pairing/blake2f/point-eval)** | Y (Solidus frames the staticcall calldata; result responder-answered) | partly (no lanes; framing only) | Y | wrong-value (framing bytes) | **P1** |
| 9 | **ABI encoder deep edges: fn-type element, tuples-in-tuples, nested `T[][]`/`string[]` round-trips** | Y (re-derives ABI layout) | Y | partly (codec well-mined at shallow depth) | wrong-value (bytes) | **P2** |
| 10 | `abi.encodeWithSelector`/`encodeWithSignature` dynamic-arg edges | Y | Y | partly | wrong-value (bytes) | **P2** |
| 11 | `abi.encodeCall` arg-tuple type-match acceptance | N (acceptance rule) | Y | partly | wrong-accept/reject | **P2** |
| 12 | `blockhash`/`blobhash` window-bound acceptance | partly (responder-answered) | Y | partly | completeness / wrong-value at boundary | **P2** |
| 13 | Event/error encoding deep corners (anonymous topic layout, indexed-ref hashing edges) | Y (re-derives topic bytes) | Y | partly | wrong-value (topic/data bytes) | **P2** |
| 14 | `type(C).creationCode`/`runtimeCode` concrete bytes | Y | N (opaque by design) | — | none-observable | **OOS** |

**P0 (do first): items 1–4.** Two are landing existing wrong-value fixes (DL1,
M1); two are UNEXPLORED abstraction-vs-concrete surfaces (low-level-call bubbling,
transient slot order) that match the V1/DL1/M1 profile most closely.

---

## 3. Sequenced review rounds

Rounds ordered by priority. Each names its target surfaces, the specific
abstraction/re-derivation risk to probe, expected reachability, and what a probe
would look like. Note the two open fixes (DL1, M1) gate rounds that re-audit their
neighborhoods — sequence those rounds to run *after* the fix lands (or to review
against the corrected code the fix agent produces).

### Round-9 — Open-world call-return & revert bubbling (P0, UNEXPLORED)
- **Targets.** `address.call`/`staticcall`/`delegatecall` low-level return
  (`(bool ok, bytes memory ret)`) and revert propagation; the returndata a failed
  external call exposes to the caller and to `try/catch`; nested revert bubbling
  (callee reverts with `Error(string)` / `Panic(0x..)` / custom error / empty →
  what the caller observes via `ok`, `ret`, and `bubble-up`).
- **Abstraction/re-derivation risk.** The open-world responder model
  (`Interpreter.lean` interaction monad, `OpenWorld`/`postWorld`) re-derives the
  returndata and the success flag rather than executing the callee. Exactly the V1
  class: a *revert-encoding / returndata* re-derivation that can silently differ
  from concrete EVM (e.g. `revert(0,0)` vs a Panic word, or truncated returndata,
  or `delegatecall` writing the *caller's* storage vs Solidus modeling it as a
  query).
- **Reachability.** DIFFERENTIALLY-LIVE — `low-level-call-options`,
  `high-level-call-options`, `try-catch` lanes exist but drive success / a single
  revert shape; the OOB corners (bubbled Panic bytes, empty-return on failed call,
  `staticcall` state-write attempt) are corpus-missed.
- **Probe shape.** For each of the three call kinds: callee that reverts with
  each of {empty, `Error("x")`, `Panic(0x11)`, custom `E(uint)`}; caller inspects
  `(ok, ret)` and re-`revert`s the raw bytes; compare Solidus's returndata to
  Forge/EVM byte-for-byte. Plus `delegatecall` storage-slot write observability.

### Round-10 — Layout-order family, post-DL1 (P0/P1, rides DL1 fix)
- **Targets.** (a) Transient-storage (`tstore`/`tload`) slot allocation ORDER
  across a non-trivial diamond; (b) storage packing across the inheritance
  boundary re-audited against the *corrected* reverse-C3 order; (c) constructor /
  inline-initializer execution order re-confirmed post-fix.
- **Abstraction/re-derivation risk.** Transient vars are allocated through the
  *same* `storageOrder` traversal DL1 miscomputes — so transient slots inherit the
  DFS-vs-reverse-C3 bug for a diamond. Packing cursor (`storageFieldAndNext`) is
  faithful *per order* but its interaction with the corrected order is unverified.
- **Reachability.** DIFFERENTIALLY-LIVE — transient storage is laned
  (`reentrancy-adoption`); a diamond with transient state vars is corpus-missed.
- **Probe shape.** The DL1 minimal repro (`Z is Y, M / M is X, Y`) with the state
  vars marked `transient`; compare `tload` slot assignment and a
  read-after-write across the diamond to solc's `--combined-json storage-layout`
  transient section (and a Forge transient round-trip). Re-run the DL1 storage
  probe against the fixed code to confirm the packing cursor still agrees.

### Round-11 — create/create2/selfdestruct observables + precompile framing (P1)
- **Targets.** `new C{value:v, salt:s}(args)` and `selfdestruct(a)` execution
  observables: deployed-contract address handling, balance movement to/from the
  new/destroyed account, deploy-revert bubbling (constructor reverts → what the
  creator observes); and Solidus's own calldata FRAMING for staticcalls to
  precompiles 0x05–0x0a (modexp length-prefix layout, ec-point encodings, blake2f
  rounds field, point-eval input) — the results are responder-answered, so only
  the *framing bytes Solidus emits* are the divergence surface.
- **Abstraction/re-derivation risk.** The open-world/postWorld model re-derives
  create/selfdestruct balance-and-address observables; a mis-framed precompile
  calldata is a value re-derivation (same class as V1).
- **Reachability.** create/selfdestruct DIFFERENTIALLY-LIVE (laned happy-path);
  precompile framing beyond 0x01–0x04 is UNEXPLORED and largely corpus-absent
  (no modexp/ec-ops lanes). create2 *address prediction* stays OOS (G22, needs
  initcode-as-bytecode).
- **Probe shape.** Constructor-reverts-on-deploy → creator's observed revert /
  returned address; `selfdestruct` then read `.balance` of both accounts. For
  precompiles: a contract that `staticcall`s 0x05 with a hand-built modexp input
  and returns the raw framed calldata length/layout; confirm Solidus frames the
  identical bytes solc's IR would.

### Memory-round-3 — M1 family completion (P1, rides M1 fix)
- **Targets.** Memory-ref aliasing across the internal-call boundary (passing
  `arr[i]` / `s.field` / a ternary / a memory-returning call as an argument);
  tuple-destructuring declaration/assignment of multiple memory refs
  (`(uint[] memory a, uint[] memory b) = f();`); byte-exact `abi.encode` of nested
  memory aggregates re-derived (relied on prior codec rounds, not re-derived in
  memory-review).
- **Abstraction/re-derivation risk.** Same id-keyed memory graph as M1: whether a
  callee parameter aliases the caller's object, and whether tuple-destructure
  threads the ref or the deref'd value, both hinge on the same ref-vs-deref
  decision M1 mis-makes.
- **Reachability.** DIFFERENTIALLY-LIVE (importer emits the statements verbatim);
  corpus-missed. Sequence after the M1 fix so the review confirms the fix reaches
  the whole family, not just the two headline shapes.
- **Probe shape.** Forge probes mirroring the M1 alias matrix but at the call
  boundary and through tuple destructure; compare post-mutation reads of the
  source aggregate.

### Round-12 — ABI encoder deep edges + acceptance mop-up (P2)
- **Targets.** Function-type element inside a tuple, tuples-in-tuples, deeply
  nested `T[][]` / `string[]` encode+decode round-trips; `abi.encodeWithSelector`/
  `encodeWithSignature` dynamic-arg edges; `abi.encodeCall` arg-tuple type-match
  acceptance; `blockhash`/`blobhash` out-of-window acceptance; event/error deep
  encoding corners (anonymous topic layout, indexed-reference hashing).
- **Abstraction/re-derivation risk.** ABI layout re-derivation at depths the
  codec rounds under-sampled; topic-byte re-derivation. Lower risk (codec was
  WELL-MINED-CLEAN at shallow depth) but the deepest nestings are least mined.
- **Reachability.** DIFFERENTIALLY-LIVE but partly corpus-covered; mostly a
  confirm-or-refute mop-up. Expect earned negatives.
- **Probe shape.** Round-trip a `(function() external, (uint,(bytes,uint8)[]))`
  through `abi.encode`/`decode` at the external boundary; compare to Forge.

---

## 4. Campaign-done criterion

The differentially-live surface is exhausted when **all** hold:

1. **Every abstraction-vs-concrete surface in the ledger (§1) is reviewed to the
   rule on both sides** — i.e. no row remains UNEXPLORED or PARTIALLY-REVIEWED in
   the "uses an abstraction or re-derives a concrete solc behavior" class
   (backlog items 1–10, 13). Items 11–12 (acceptance) and 14 (OOS-bytes) may
   remain unreviewed without blocking the criterion, since acceptance-only rules
   are importer-masked on a solc-validated corpus.
2. **Both open wrong-value fixes (DL1, M1) have landed and their neighborhoods
   re-audited** (Round-10, Memory-round-3) with the fix confirmed to cover the
   whole family, not just the headline shape.
3. **Two consecutive review rounds produce zero new differentially-live findings**
   (the round-5 "earned negative" signature) — the signal that reviews have hit
   true diminishing returns rather than merely pausing between productive veins.

Until (3), the loop is still in the productive phase and should keep scheduling
rounds from §3. When (1)+(2)+(3) all hold, remaining work is acceptance-oracle
hardening and OOS items only, and the differential-review campaign is done.

---

## 5. Notes on method (reuse the established convention)

- **Per-round doc.** One `docs/solc-implementation-divergences-N.md` (or a named
  `-memory-`/topic doc) per round. Cite **solc file:line on BOTH sides**
  (`solidity-src/...` and `SolidCore/Solidity/*.lean` / importer line), classify
  each finding's **reachability** (DIFFERENTIALLY-LIVE / IMPORTER-MASKED /
  UNTESTED / OOS) and **confidence** (CONFIRMED = both sides read + probe;
  INFERRED = code trace), and **build on prior rounds** (open with what the
  earlier docs established so the frontier is explicit). Keep the
  surfaces-reviewed-vs-still-not-reached worklist at the tail so the next round
  inherits a live backlog.
- **Probes, not builds.** Read-only. Use the pinned `solc 0.8.35`
  (`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) for tiny
  accept/compile/`--combined-json storage-layout` probes and Forge for concrete
  EVM ground truth; do **not** build/run Solidus. Mark findings CONFIRMED only
  when both sides are read to the rule (+ probe where an observable is claimed).
- **Severity ladder.** wrong-value > wrong-order > wrong-accept/reject >
  completeness. Foreground the abstraction-vs-concrete surfaces; a re-derivation
  that silently differs on a corpus-missed input is the campaign's whole thesis.
- **Parallelization / worktree.** Independent rounds run concurrently in separate
  git worktrees; a review round adds only its one doc, so it rebases cleanly onto
  sibling fix commits (`git pull --rebase`, re-stage the doc, retry) even while a
  fix agent commits to the same branch. Sequence the fix-gated rounds (Round-10
  post-DL1, Memory-round-3 post-M1) to review against the fix agent's landed code.
