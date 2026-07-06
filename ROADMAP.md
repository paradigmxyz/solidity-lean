# Roadmap: Solidity Source Semantics — Cleanup and Composition-Readiness

## Goal

Turn this repository into a clean, genuine, executable Lean semantics of
Solidity 0.8.35 whose external-world model is expressed in the **same
interaction monad** (`Simulation.Interaction` over the `Query`/`OpenWorld`
alphabet) used by the Yul source semantics and EVM target semantics in
`../evm-compiler` (Solidus), on the **same Lean toolchain and EVMYulLean pin**,
validated end-to-end by the existing pinned-solc/Forge differential corpus.

**Non-goals for this phase.** No Solidity→Yul lowering, no `ForwardRel`
proofs, no repo merge with `evm-compiler`. The eventual lowering will be built
the way Solidus was built — horizontal layers from the bottom up, each layer a
complete verified abstraction over the one below — but that is a future goal
with its own roadmap. This phase only has to leave the source semantics in a
shape where that future project can start without re-plumbing.

**Definition of done for this phase** (all together):

1. Builds on `evm-compiler`'s exact toolchain (Lean v4.28.0) against the same
   `danrobinson/EVMYulLean @ 3c5c44a6` pin as a real Lake dependency; the
   local `EvmYul.UInt256`/Keccak compatibility shims and the
   `external/nethermind` submodule are gone.
2. The interaction monad, `Query`, `OpenWorld`, and `ForwardRel` are imported
   from a shared package whose types are definitionally identical to the ones
   in `evm-compiler`'s public theorems.
3. The interpreter's only channel for external effects (calls, creates) is
   that shared query alphabet; the oracle-record `Context` fields for
   calls/creates are deleted.
4. Exactly one expression evaluator and one statement evaluator remain.
5. The observation layer is deleted.
6. No semantics file is a monolith: AST, typechecker, elaboration,
   interpreter, ABI, and witness corpus live in separate modules.
7. The full differential corpus replays green (with a documented,
   intentional delta for pruned observation-only assertions).
8. Known semantic gaps are recorded in this file, not silently absent.

## Decisions already made

- **Substrate**: match `evm-compiler` exactly (Lean v4.28.0,
  `danrobinson/EVMYulLean @ 3c5c44a6`); do not bump either side.
- **Interaction monad sharing**: extract a small standalone Lake package both
  repos depend on; `evm-compiler` re-exports under its existing names.
- **Semantic gap fixes** (balance accounting, rational constant folding,
  `gasleft` as a resource query): **deferred**, recorded in the gap registry
  below. This phase is structural.
- **Observation layer**: delete all of it; prune or re-express the harness
  witnesses that referenced it.
- **Conformance corpus**: kept, frozen as a regression oracle. No new
  acceptedness/coverage slices during this phase.

## Current state (analysis)

What exists, as of the checkpoint commit:

- **One coherent fuel-based interpreter** in
  `SolidCore/Solidity/Interpreter.lean` (~12k lines): `Stmt.eval` (mutual
  with loop/list evaluators), `FunctionDef.call?`, `Contract.call?` /
  `callTransaction?`, plus full ABI dispatch in `SolidCore/Solidity/ABI.lean`.
  Total, zero `sorry`/`axiom`/`partial`.
- **A surface AST + typechecker + elaboration** in
  `SolidCore/Spine/L00_SourceSolidity/{Interface,TypeCheck,Checked}.lean`
  (~109k lines combined), of which roughly **two thirds is hand-written
  witness corpus** inside `namespace Examples` blocks, and ~20k lines is
  elaboration plus an observation layer.
- **A strong differential harness**: 98 paired cases (real OpenZeppelin,
  WETH9, solmate, Uniswap, Compound), 420 Lean eval assertions, ~309
  pinned-solc rejection lanes, and a fail-closed solc-AST importer with zero
  unimplemented node types over the corpus.

Structural problems this roadmap exists to fix:

- **External world as oracle records.** External calls, creates, account
  lookups, and low-level results are functions/tables stored in `Context`
  (`Interpreter.lean` ~1928–1953 is the choke point). Solidus's semantics
  instead *emit* each external effect as a `Query` in a free-monad
  interaction tree and continue on the environment's `Answer`. `ForwardRel`
  — the composition relation all of Solidus's theorems are stated in —
  requires both sides of a refinement to emit **identical queries** and
  resume on **identical answers**. An oracle-record semantics cannot appear
  on the left of that relation without a rewrite. This is the single
  load-bearing refactor of the whole phase.
- **Substrate skew.** This repo: Lean v4.29.1, local `EvmYul.UInt256` and
  Keccak shims, reference submodule `NethermindEth/EVMYulLean @ 047f630`.
  `evm-compiler`: Lean v4.28.0, `danrobinson/EVMYulLean @ 3c5c44a6`
  (branch `djtotal`) as a Lake dependency. `State`, `SharedState`,
  `Substate`, and `UInt256` must be *literally the same types* for any
  future cross-repo statement, so the shims must go.
- **Four generations of expression evaluators** coexist in
  `Interpreter.lean` (`Expr.eval`, `evalWithRuntime`,
  `evalWithRuntimeOrderFuel`, `evalWithRuntimeByContext`); only the last is
  used by `Stmt.eval`, but older ones are still referenced from elaboration
  code.
- **33 `*Observation` structures** plus per-construct `observe*` walkers,
  built speculatively as a "future preservation interface," used in zero
  theorems. The interaction-tree design supersedes their role: the actual
  composition interface is the query transcript plus a done-relation on
  final states, not bespoke per-construct records.
- **Monoliths.** `Interface.lean` is 52k lines because AST, elaboration,
  observations, and a 31k-line example corpus share one file. Same pattern
  in `TypeCheck.lean` and `Checked.lean`.
- **Vestigial naming.** `SolidCore/Spine/L00_SourceSolidity/` is left over
  from the removed compiler-spine layout ("L00" of layers L00–L06 that no
  longer exist here).

## Target architecture

```text
shared package (new, extracted from evm-compiler):
  Simulation.Interaction  -- free monad: done | request (query) (answer → k)
  Query / Answer          -- resource (gas|msize) | external (OpenWorld, ExternalRequest)
  OpenWorld               -- accounts (nonce, balance, storage, transient, code), substate
  ForwardRel + trans/mono/bind lemmas

this repo:
  SolidCore/Solidity/Ast.lean          -- surface AST (moved from Interface.lean)
  SolidCore/Solidity/TypeCheck/…       -- common checker (split)
  SolidCore/Solidity/Elab/…            -- surface → core elaboration (split)
  SolidCore/Solidity/Core/…            -- core language, values, state, memory model
  SolidCore/Solidity/Interp/…          -- ONE evaluator, monadic in the shared Interaction
  SolidCore/Solidity/Abi/…             -- ABI encode/decode/dispatch
  SolidCore/Solidity/Entry.lean        -- checked entry points (construct?/call/transaction)
  SolidCore/Witness/…                  -- the entire example corpus, out of the semantics
  tests/forge-harness/…                -- unchanged differential corpus (frozen)
```

The interpreter's public type becomes (schematically):

```
Contract.call : Fuel → Env → Contract → CallInput → SourceState
              → Interaction SolidityFailure SolidityCallResult
```

where `Interaction`, `Query`, `Answer` are the shared package's types, and a
leaf `done` carries the Solidity-owned final state (typed storage, events,
returns/reverts). The *only* nodes in the tree are external calls/creates
(and, later, resource queries when `gasleft` is un-deferred).

## Phase 1 — Substrate unification

Move to `evm-compiler`'s exact substrate before touching semantics, so every
later phase rebuilds against the final types once.

Steps:

1. Set `lean-toolchain` to `leanprover/lean4:v4.28.0`; align the Mathlib
   revision with `evm-compiler`'s `lake-manifest.json`.
2. Add `danrobinson/EVMYulLean @ 3c5c44a6` as a Lake dependency (same
   ref/branch as `evm-compiler`).
3. Delete `EvmYul/UInt256.lean`, `SolidCore/../Keccak` shim contents, and the
   `external/nethermind/EVMYulLean` submodule; rewire `SharedSemantics/*`
   adapters to the real pinned types (`EvmYul.UInt256`,
   `EvmYul.SpongeHash.Keccak256`, block/account/log/substate types).
   `SharedSemantics` may shrink to thin, named re-exports; keep the
   source-facing names stable so the interpreter diff stays small.
4. Full corpus replay.

Analysis / risks:

- **Toolchain downgrade** (4.29.1 → 4.28.0) can surface syntax/elaborator
  differences in 130k lines. Expect mechanical fixes; do them before any
  semantic change so failures are attributable.
- **Keccak behavior**: the local shim and the pinned implementation must
  agree bit-for-bit; the corpus's hash-heavy cases (ECDSA, MerkleProof,
  event topics, selectors) are the check. Any expectation change here is a
  bug, not a delta to accept.
- The pinned repo's own `partial`/`native` usages are outside our proof
  surface for now, but note them; they matter when theorems arrive.

Acceptance: `lake build` green on v4.28.0; complete paired replay green with
**zero** expectation changes; no local copies of pinned-package types remain.

## Phase 2 — Extract the shared interaction package

Create a new standalone Lake package (working name: `evm-interaction`)
containing exactly the composition-critical vocabulary from `evm-compiler`:
`Simulation.Interaction` (the free monad, `Transcript`, `ForwardRel` and its
`trans`/`mono`/`strengthen_right`/`bind_right` lemmas), `Query`/`Answer`,
`ResourceQuery`, `ExternalRequest`/`CallRequest`/`CallResponse`/
`CreateResponse`, and `OpenWorld` (+ its `ofYulShared`/`ofEVMShared`
projections). It depends only on the EVMYulLean pin (and Mathlib if needed).

Analysis / risks:

- **The freeze problem.** Parts of `evm-compiler`'s Simulation framework are
  hash-frozen for the Solidus challenge. If re-exporting from the shared
  package would require editing frozen files, `evm-compiler` cannot adopt
  the package until the next challenge version bump. **Fallback:** the
  shared package is created as a *file-identical extraction* (same
  namespaces, same declarations), this repo depends on it, and a CI script
  hash-compares the extracted files against `evm-compiler`'s copies so
  drift is mechanically impossible. `evm-compiler` switches to the package
  whenever its freeze is next rev'd. Either way, this repo programs against
  the real alphabet from day one.
- Keep the package **minimal**. Do not pull in Yul semantics, effect
  semantics, or anything Solidus-implementation-shaped. The package is the
  *language of composition*, not a semantics library.
- Namespace choice matters: if the extraction keeps `Simulation.*` and
  `EvmCompiler.Simulation.*` re-exports, the frozen theorem statements
  remain textually unchanged when `evm-compiler` adopts it.

Acceptance: this repo imports the package; a hash-check script proves the
package's files match `evm-compiler`'s current Simulation sources; both repos
build.

## Phase 3 — De-monolith: witnesses out, modules split, one evaluator

All mechanical, all behavior-preserving, done before the interaction rewrite
so that Phase 5 edits small files.

1. **Move every `namespace Examples` block** out of
   `Interface.lean`/`TypeCheck.lean`/`Checked.lean` into
   `SolidCore/Witness/…`, preserving declaration names so the harness's
   generated `#eval` lines keep resolving (the harness imports a module and
   evaluates `*Matches` defs by name; only the import target changes).
2. **Split the semantics files** along the target layout above:
   `Ast.lean` (the ~445-line surface AST), elaboration modules, typechecker
   modules, core-language modules, ABI. Rename the module tree away from
   `Spine/L00_SourceSolidity` (vestigial) to `SolidCore/Solidity/…`, keeping
   deprecated re-export stubs for one commit if it eases the harness cutover.
3. **Consolidate evaluators.** `Expr.evalWithRuntimeByContext` (the one
   `Stmt.eval` uses) becomes *the* evaluator; port the elaboration-side
   references to the older three generations (`Expr.eval`,
   `evalWithRuntime`, `evalWithRuntimeOrderFuel`) and delete them. Any
   behavioral difference discovered while porting is a latent bug — pin it
   with a corpus case before changing anything.
4. Re-run the full corpus after each of the three sub-steps, not just at the
   end.

Analysis / risks:

- The witness move is 70k+ lines of cut-and-paste; the danger is silent
  name-capture changes (open namespaces, section variables). Mitigate by
  moving whole `namespace` blocks verbatim and letting the compiler find the
  missing opens.
- Splitting mutual blocks across files is not possible in Lean; the
  interpreter's big mutual block stays in one file, but examples,
  observations (until Phase 4), state definitions, and helper layers around
  it move out. "No monolith" means no *mixed-concern* file, not an arbitrary
  line limit on the mutual core.

Acceptance: corpus green and assertion-count identical; `Interface.lean` no
longer exists (or is a re-export stub); exactly one expression evaluator.

## Phase 4 — Delete the observation layer

Remove all 33 `*Observation` structures, the `observe*` walker functions, and
their support code from the semantics modules.

For each harness assertion that referenced an observation:

- If it checks **behavior** (a return value, revert payload, storage
  readback, event, call result), re-express it against the plain
  interpreter results (`CallResult`, `State`, log entries) and keep it.
- If it checks only the **observation record itself** (e.g. that a walker
  reports the branch that was taken, or packages fields a certain way),
  drop it and record the drop.

Analysis:

- Rationale for full deletion rather than selective keep: the observation
  records were designed as a preservation interface for a Yul relation, but
  `ForwardRel` composition needs (a) the query transcript — which the
  Phase 5 interaction trees provide natively — and (b) a done-relation on
  final states — which needs the *state itself*, not per-construct event
  records. Keeping them would preserve ~20k lines of walkers that shadow the
  evaluator per-construct and must be co-maintained with every semantic
  change. They are the clearest "going in circles" artifact; they go.
- The deletion will reduce the manifest's `lean_evals` count. That delta
  must be **enumerated in the commit message** (which assertions, why each
  is either re-expressed or observation-only) so no behavioral coverage is
  lost silently.

Acceptance: zero `Observation` declarations in the semantics; corpus green;
documented assertion delta with every dropped assertion classified.

## Phase 5 — External world as the shared interaction monad

The centerpiece. Rewrite the interpreter's external boundary so that a
Solidity execution *is* an `Interaction` tree over the shared `Query`
alphabet.

Design:

1. **Monad.** Define `SolI α := Simulation.Interaction SolidityFailure α`
   (exact shape to be settled against the shared package; the constructor
   alphabet is non-negotiable, the Failure/Result payloads are
   Solidity-owned). Thread it through the `Stmt.eval`/`Expr.eval` mutual
   block. The interpreter is already total via fuel; the tree is finitely
   deep for the same reason, so totality is preserved without `partial`.
2. **What becomes a request.** Exactly the effects Solidus's Yul semantics
   treats as requests: external calls (all kinds: call/staticcall/
   delegatecall, low-level and high-level, send/transfer, external
   function-pointer calls, try targets) and contract creations
   (`new`, create/create2 with value/salt). Each becomes a
   `Query.external world request` node built at the current choke points
   (`Interpreter.lean` ~1928–1953 and the creation analog), continuing on
   the `CallResponse`/`CreateResponse` answer.
3. **The `OpenWorld` snapshot problem** — the key design issue. Solidus's
   `Query.external` carries a concrete `OpenWorld` (word-addressed storage,
   balances, nonces, code). This repo's storage is deliberately typed and
   abstract, so today it *cannot* produce that snapshot. Two sub-decisions:
   - **Storage layout becomes part of the source semantics.** Unlike
     compiler memory layout, Solidity's storage layout (slots, packing,
     mapping/array slot derivation) is *documented language spec* — it is
     what upgradeable-contract and cross-contract tooling relies on — and
     the repo already models slots/packing/paths internally (the packed-
     storage and storage-path machinery). Promote that to the semantics: a
     total layout encoding from typed source storage to word storage,
     defined once, used to materialize the snapshot at each request. Memory
     stays abstract (memory reaches queries only through ABI-encoded
     calldata bytes, which the ABI layer already concretizes).
   - **Non-self accounts** (balances, code, nonces of other addresses) stop
     being ad hoc oracle lookups and become reads of a `OpenWorld`-shaped
     environment carried in the source state — mirroring how Yul reads its
     `SharedState` without emitting queries. Post-answer, the
     `CallResponse.postWorld` replaces that environment. The self account
     needs care: the answer may legitimately change *our own* storage words
     (reentrancy), but the layout encoding `E : TypedStorage → WordStorage`
     has no computable inverse in general (non-image word states; keccak-
     derived mapping slots are unattributable without knowing the key).
     Resolution for this phase — **fail-closed re-projection**: diff the
     answered self-storage words against the snapshot we sent; unchanged →
     keep the typed state; changed slots attributable to known typed paths
     (static layout, plus mapping/array keys the execution has touched)
     with clean field encodings → decode back; anything else → distinguished
     execution failure rather than guessing. This makes "layout-respecting
     environments" an **explicit assumption** the future composed theorems
     quantify over (realizable reentrancy satisfies it, since reentrant
     writes go through our own code and hence through `E`). Known escape
     hatch if that assumption ever chafes: flip self-storage to word-backed
     state with typed reads/writes as layout views (read-with-cleanup,
     matching deployed-code behavior) — absorbs any postWorld trivially and
     is plausibly the lowering-era representation; not this phase.
4. **Failure/result mapping.** Solidity reverts/panics map to a
   Solidity-owned `Failure` payload; the final `done` leaf carries the rich
   source state. No attempt yet to relate these to Yul's `Exception` — that
   relation *is* the future lowering's done-relation, and prematurely
   flattening the source state would repeat the observation-layer mistake
   in a new costume.
5. **Harness conversion.** Fixture oracle tables (`lowLevelCallResults`,
   creation results, account facts) become **scripted responders**: a
   deterministic `(q : Query) → Answer q` (in practice a replay list with
   fail-closed mismatch reporting) derived from the same fixture data.
   Expectations should not change; where a fixture's oracle was internally
   inconsistent with any world snapshot, that is a fixture bug the
   conversion will smoke out.
6. **Delete** the oracle-record call/create fields from `Context` once
   nothing reads them. Environment reads that Yul also takes from shared
   state (block/tx fields, blockhash) stay as state reads, not queries —
   matching the alphabet exactly.

Analysis / risks:

- **This is a large mechanical rewrite of the mutual block** (threading a
  monad through every evaluator arm). Order of work inside the phase:
  define the monad + choke-point request emission first with a
  *replay-from-Context* environment so the old fixtures run unmodified;
  convert fixtures; then delete the oracle fields. Corpus green at each of
  the three checkpoints.
- **Performance.** The corpus already has slow lanes (the OZ royalty case).
  A free-monad interpreter adds allocation; if replay times regress badly,
  the mitigation is a fused `run` function (environment applied during
  evaluation) that is *proved-by-construction* equal to building the tree
  then folding it — but measure first.
- **Transcript determinism.** After this phase, a Solidity execution's
  external behavior is a deterministic query sequence. The deterministic
  child-evaluation-order policy (already chosen, Yul-compatible) is what
  makes this well-defined; it is now load-bearing and should be documented
  as such.
- `gasleft` stays an ambient constant this phase (deferred), but the
  request type already reserves the resource-query arm, so un-deferring it
  later is additive.

Acceptance: the only external-effect channel is the shared `Query` alphabet;
fixtures run as scripted responders; oracle-record fields deleted; full
corpus green; a short demo witness shows a two-call contract execution as an
explicit `Interaction` tree with its query transcript.

## Phase 6 — Documentation, boundary restatement, and freeze

1. Rewrite `ARCHITECTURE.md` for the new layout and the interaction-monad
   boundary; update the boundary rules: storage layout is now **in scope**
   (spec-owned), memory layout remains out; external world is the shared
   alphabet, not oracles.
2. Restate the completion claim honestly: this repo is an *executable,
   differentially-validated* semantics; verification is the corpus, not
   theorems, until the lowering project begins.
3. Freeze the conformance corpus and the typechecker-acceptedness lane
   family explicitly: they are regression suites. New lanes are added only
   to pin a *discovered bug*, not to extend coverage.
4. Refresh `tests/README.md` and the harness docs for the new module paths
   and scripted-responder fixture format.
5. Trim `PROGRESS_LOG.md` (archive the historical log to
   `docs/PROGRESS_ARCHIVE.md`; keep a short live tail).

## Known semantic gaps (deferred, recorded)

These are *not* fixed in this phase. Each gets fixed with paired Forge lanes
when picked up.

| Gap | Status | Notes |
| --- | --- | --- |
| Intra-frame balance accounting | Deferred | `msg.value` never credits the callee; `address(this).balance` and value sends read/write nothing. Real EVM credits before body execution; this is Solidity-observable. Phase 5's world environment creates the natural home for the fix. |
| Rational constant expressions | Deferred — **suspected unsoundness** | solc folds constants in unbounded-precision rationals (`1e18`, subdenominated and fractional intermediates, huge powers that cancel). No rational-folding machinery exists here; one importer path requires plain decimal naturals. Audit lane first; may currently mis-evaluate or silently reject legal programs. |
| `gasleft` as resource query | Deferred | Today a fixed ambient word. Becomes `Query.resource gas` once someone needs it; alphabet already reserves it. |
| Inline assembly | Out of scope (unchanged) | Future design sketch: an embedded-Yul statement whose meaning *is* the shared Yul semantics — cheap once both live on the same interaction substrate. Determines real-world applicability of any eventual compiler. |
| Imports / multi-file units | Out of scope (unchanged) | Flattening as an explicit, tested preprocessing step is the likely answer; currently an exclusion. |
| Closed-world multi-contract execution | Out of scope by design | The open-world query model matches Solidus; reentrancy and `this.f()` are environment-answered, never executed. |
| Gas metering | Out of scope by design | Solidus handles real gas in its gasful refinement conjunct. |

## Phase ordering and discipline

Phases run 1 → 6 in order; 3 and 4 may interleave. Every phase ends with a
full corpus replay and a commit; no phase starts on top of an uncommitted
predecessor. Rules of engagement for the whole cleanup:

- **No new coverage.** The corpus is frozen; the open-ended acceptedness
  audit from the previous roadmap is closed, not "continued."
- **No new speculative interfaces.** Anything built "for the future proof"
  must be demanded by the shared alphabet or it doesn't get built.
- **Behavior changes require a pinned lane first.** If a refactor exposes a
  semantic bug, add the differential case, then fix.
- **Expectation deltas are enumerated.** Any change to the manifest's
  assertion set is listed and classified in the commit that makes it.
