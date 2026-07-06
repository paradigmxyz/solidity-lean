# Roadmap: Solidity Source Semantics — Cleanup and Composition-Readiness

## Goal

Turn this repository into a clean, genuine, executable Lean semantics of
Solidity 0.8.35 whose external-world model is expressed in the **same
interaction monad** (`Simulation.Interaction` over the `Query`/`OpenWorld`
alphabet) used by the Yul source semantics and EVM target semantics in
`../evm-compiler` (Solidus), on the **same Lean toolchain and EVMYulLean pin**,
validated end-to-end by the existing pinned-solc/Forge differential corpus.

**This repo is only the Solidity source semantics.** Every compiler-era
artifact goes: the local `EvmYul` library and root `EvmYul.lean` (currently a
`default_target` in the lakefile), `SolidCore/Spine.lean`, the
`Spine/L00_SourceSolidity` module naming, and any remaining
"lowering"/"spine"/"L0x" vocabulary in code, docs, and namespaces. The end
state is a single `lean_lib SolidCore` whose module tree is
`SolidCore.Solidity.*` (+ `SolidCore.Witness.*`), with `SharedSemantics`
folded in or reduced to nothing once the pinned package supplies the
primitives.

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

## Implementation notes for the executor (disambiguation)

This section resolves decisions the phase descriptions leave open. The run
is **fully autonomous**: no decision waits on a human. When a situation
arises that neither the phases nor these notes cover, take the most
conservative behavior-preserving option, record what was decided and why in
`docs/DECISIONS.md` (create it; one dated entry per decision), and continue.
If a phase is genuinely stuck after serious attempts, record the blocker in
`docs/DECISIONS.md` and move to the next phase that does not depend on it
(dependencies: Phase 2 needs Phase 1; Phase 5 needs Phases 2–4; Phases 3–4
need nothing but each other's ordering). End the run with a summary entry in
`docs/DECISIONS.md`: phases completed, corpus status, every deviation.

### Hard rules

- **Never modify `/Users/dan/Projects/evm-compiler`.** Not its frozen files,
  not its unfrozen files, not its lakefile. It is read-only reference and
  extraction source.
- **Never edit fixture `.sol` sources or Forge tests** except (Phase 5) the
  mechanical oracle-table → scripted-responder conversion and (Phase 3)
  import-path/namespace string updates in `manifest.json` and the scripts.
- **A "green" full replay means, verbatim:**
  `FORGE=/Users/dan/.foundry/bin/forge scripts/compare_forge_solc_interpreter.sh --timeout 900`
  exits `status=0` with `forge_interpreter_compare=pass`, `cases=98`,
  `paired_cases_passed=yes`; and the AST audit
  (`python3 scripts/audit_solc_ast_frontend.py`) reports
  `rendered_sources=sources`, `render_failures=0`, and zero
  unimplemented/unclassified counts. A replay interrupted mid-run counts as
  **not run** (this has caused false confidence before; see the 2026-06-30
  progress-log entries). The full replay takes ~20+ minutes; the
  `frontend-frontier` and `openzeppelin-erc721-royalty` lanes are slow but do
  complete.
- **Renames are three-sided.** Lean namespaces are duplicated as strings in
  `tests/forge-harness/manifest.json` (`lean.imports`, every `lean.evals[].expr`,
  every `solc_import.namespace`) and generated by
  `scripts/solc_ast_to_lean_source.py`. Any module/namespace rename must
  update all three mechanically in the same commit, and the manifest's eval
  count must not change.

### Phase 1 specifics

- Copy `evm-compiler`'s pins wholesale: `lean-toolchain` verbatim, and the
  Mathlib + EVMYulLean entries from its `lake-manifest.json` (same revs), so
  transitive pins cannot skew.
- Keccak: retarget `SolidCore/Solidity/Keccak.lean`'s re-exports at the
  pinned package's `EvmYul.SpongeHash.Keccak256` (same declaration names).
  Use the same entry points `evm-compiler`'s Yul semantics uses. If the
  pinned implementation turns out to be `partial`/IO-backed and unusable
  from a total interpreter, **keep** the local pure implementation, rename
  it to make local-ness explicit, and add a corpus-checked byte-parity
  witness against the pinned one — do not silently keep a shim.
- Toolchain-downgrade fixes must be mechanical (syntax, elaborator quirks).
  If a fix would change behavior, pin a corpus lane first, then fix, and
  log it in `docs/DECISIONS.md`.
- Delete in this phase: `EvmYul/` and `EvmYul.lean`, the `lean_lib EvmYul`
  target, `external/nethermind/` (submodule + `.gitmodules` entry).

### Phase 2 specifics

- The shared package is a **new sibling git repo** at
  `/Users/dan/Projects/evm-interaction`, consumed from this repo via a Lake
  path dependency (`require` … `from "../evm-interaction"`). Promote to a
  git URL later; do not block on it.
- Extract the minimal transitive closure of: `Simulation.Interaction`,
  `Transcript`, `Query`/`Answer`, `ResourceQuery`, `ExternalRequest`,
  `CallRequest`/`CallResponse`/`CreateResponse`, `OpenWorld` (+
  `ofYulShared`/`ofEVMShared`), `ForwardRel` and its composition lemmas
  (`trans`, `mono`, `strengthen_right`, `bind_right`). Start from
  `EvmCompiler/Simulation/Interaction.lean` and follow imports. Files are
  copied **verbatim** — same namespaces, same declaration names — so the
  hash-check script (lives in this repo, reads `../evm-compiler` read-only)
  can compare byte-for-byte. If the closure drags in Yul/EVM semantics
  files, do not extract those: narrow the package to what separates
  cleanly, vendor the entangled remainder verbatim **inside this repo**
  under the same hash-check, and log the entanglement in
  `docs/DECISIONS.md`. If even the minimal package cannot be separated,
  skip the sibling package entirely and vendor everything here with the
  hash-check — the alphabet identity is what matters, not the packaging.

### Phase 3 specifics

- Sub-step order, corpus replay after each: (a) move `Examples` namespaces
  out verbatim into `SolidCore/Witness/…` (keep the *namespace names*
  unchanged inside the new files so manifest `expr` strings still resolve;
  only `lean.imports` entries change); (b) split the semantics modules and
  do the `Spine/L00_SourceSolidity` → `SolidCore.Solidity` rename with the
  three-sided manifest/script update; (c) fold `SharedSemantics` into
  `SolidCore/Solidity/Shared/…` (or delete adapters that became trivial
  re-exports) and reduce the lakefile to the single `lean_lib SolidCore`;
  (d) evaluator consolidation.
- Evaluator consolidation: if switching a call site from an older evaluator
  generation to `evalWithRuntimeByContext` changes **any** corpus result,
  that difference is a latent bug, not a porting detail. Resolve it
  autonomously with the corpus as arbiter: pin the divergence with a
  focused lane, adopt whichever behavior matches Forge/pinned-solc, and
  log the divergence and resolution in `docs/DECISIONS.md`.

### Phase 4 specifics

- **Trap: storage-layout machinery is not observation code.** `StorageLayout`,
  `StorageLayoutCursor`, `slotSpan`, `Context.storageSlot?`, and the
  packing/path-resolution functions in `Interpreter.lean` are core semantics
  (Phase 5 depends on them; they move to
  `SolidCore/Solidity/Core/StorageLayout.lean`). Only the `*Observation`
  record types, the `observe*` walkers, and their support glue are deleted.
  Rule of thumb: if deleting it would change what the interpreter *computes*
  (not what it *reports*), it is not observation code.
- Classification procedure per affected manifest eval: if the witness
  compares data that Forge can observe (return values, revert bytes, storage
  readback, logs, call results), re-express it against `CallResult`/`State`
  and keep it; if it only inspects observation-record structure, drop it.
  Mixed witnesses are split, not dropped. Record every disposition in
  `docs/phase4-assertion-delta.md` (a file, not just the commit message).

### Phase 5 specifics

- Interpreter entry points keep their names (`Contract.call`,
  `callTransaction`, ABI entries); the return type changes from
  `Option Result` to the interaction tree. **Fuel exhaustion becomes a
  distinguished failure constructor** (mirroring Yul's `.OutOfFuel`
  truncation arm), not an `Option` wrapper — this is what the future
  truncation-reflection side condition of `ForwardRel.trans` needs.
- What becomes a query: all external calls and creates **including**
  public/external library `delegatecall`s and address-keyed precompile
  calls (Solidus treats precompile calls as environment-answered external
  requests; match it). Internal calls, free functions, internal library
  calls, and bound `using` methods stay internal.
- `CallRequest.requestedGas` is a mandatory `Word`. With gas deferred, fill
  it from the explicit source `{gas: …}` option when present, else from the
  ambient `gasleft` constant. **Do not attempt** the 63/64 rule or any gas
  arithmetic — exact gas-query alignment with generated Yul is explicitly
  part of the deferred `gasleft` work, and the transcript-level mismatch it
  leaves is a recorded limitation, not a bug to fix now.
- Scripted responder format: a per-fixture ordered list of
  (request-matcher, response) pairs derived mechanically from the existing
  oracle tables, applied fail-closed — an unmatched or out-of-order request
  is a test failure with a diff of expected vs actual request. Expectations
  must not change. A fixture whose oracle data cannot be expressed as a
  consistent responder is a fixture bug: correct the responder data
  minimally so it is world-consistent while the paired Forge test remains
  the authority on observable behavior, and log the inconsistency and the
  correction in `docs/DECISIONS.md`.
- Sub-step order, corpus replay after each: (1) introduce the monad and emit
  requests at the existing choke points, with a temporary
  replay-from-`Context` environment so fixtures run unmodified; (2) convert
  fixtures to scripted responders; (3) delete the oracle-record `Context`
  fields. Time the full replay before (1) and after (3); if wall-clock
  regresses more than ~2×, implement the fused `run` (environment applied
  during evaluation) and check it against the tree-then-fold semantics on
  the corpus.

### Autonomous fallback policies (formerly stop-and-ask)

- **Something seems to require editing `evm-compiler`.** It never does for
  this phase's purposes: fall back to verbatim vendored copies plus the
  hash-check (see Phase 2 specifics). If a fallback still fails, log it and
  defer that sub-goal; do not touch `../evm-compiler`.
- **A corpus expectation seems wrong.** The pinned Forge/solc side is
  ground truth for observable behavior. If the Lean side must change to
  match Forge, that is an ordinary bug: pin, fix, log. If the *Forge-side*
  expectation itself looks wrong, leave it untouched, keep the paired Lean
  witness matching it, and log the suspicion in `docs/DECISIONS.md` for
  human review — never edit both sides to a new agreed value.
- **The shared `Query`/`OpenWorld` types cannot represent something the
  Solidity semantics needs to say.** Never fork or locally extend the
  shared types. Leave that specific construct on the old oracle path,
  clearly marked (add it to the deferred-gap registry in this file with a
  pointer to the code), convert everything else, and log it. Partial
  conversion with an explicit, enumerated residue is the correct outcome;
  an invented alphabet variant is not.

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
