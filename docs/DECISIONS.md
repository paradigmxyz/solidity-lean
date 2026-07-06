# Decisions log (autonomous cleanup run)

One dated entry per non-obvious decision taken while executing `ROADMAP.md`.
The run is fully autonomous; where the phases and implementation notes leave a
choice open, the most conservative behavior-preserving option was taken and
recorded here.

## 2026-07-06 — Phase 1: pinned Keccak is FFI/opaque, keep the pure local spec

`danrobinson/EVMYulLean @ 3c5c44a6` ships Keccak256 as an FFI symbol, not a
pure Lean function:

- `EvmYul/SpongeHash/Keccak256.lean` in the pin is an empty stub (a comment:
  "Use FFI in the meanwhile").
- The actual hash is `@[extern "keccak256"] opaque keccak256 (input : ByteArray)
  (len : USize) : ByteArray` in `EvmYul/FFI/ffi.lean`.

An `opaque`/`@[extern]` function is unusable from this repo's total, purely
computational fuel interpreter: it does not reduce, cannot be `#eval`'d without
native linking, and carries no equational content for future theorems.

Decision (matches ROADMAP Phase 1 specifics fallback, verbatim: "If the pinned
implementation turns out to be `partial`/IO-backed and unusable from a total
interpreter, keep the local pure implementation, rename it to make local-ness
explicit, and add a corpus-checked byte-parity witness against the pinned one —
do not silently keep a shim"):

- Only `EvmYul.UInt256` retargets to the real pinned type (it is a pure,
  reducible `structure ... deriving`, and exposes every named op
  `SharedSemantics.Word` uses).
- The pure Keccak stays, moved out of the `EvmYul.*` namespace into a clearly
  repo-owned module, so nothing masquerades as an upstream shim.
- A byte-parity witness against the pinned FFI keccak is added where the build
  can link it; if native linking of the extern symbol is not available in the
  witness/harness path, that is recorded as a limitation here rather than
  silently skipped.

## 2026-07-06 — Phase 1: reuse the sibling build's prebuilt dependency tree

`../evm-compiler` already has `danrobinson/EVMYulLean @ 3c5c44a6` + its Mathlib
pin built against the exact same toolchain (Lean v4.28.0) this phase moves to.
Rather than a multi-hour from-scratch Mathlib + EVMYulLean build, this repo's
`.lake/packages` is seeded by an APFS copy-on-write clone of the sibling's
prebuilt package tree, and the dependency section of the sibling's
`lake-manifest.json` is reused verbatim (same revs). This is a build-cache
reuse only: `../evm-compiler` is never written to, the `require evmyul from
git ... @ 3c5c44a6` in the lakefile is the real dependency of record, and Lake
remains free to refetch/rebuild from it.

## 2026-07-06 — Phase 1: toolchain-downgrade (4.29.1 → 4.28.0) mechanical fixes

The v4.28.0 downgrade surfaced three purely mechanical, behavior-preserving
breakages. None changes what the interpreter computes; each was fixed without a
new pinned lane because there is no observable-behavior delta.

1. **`alias` is a reserved token in v4.28.0.** The struct field
   `InternalFunctionAliasBinding.alias` and a few local `let`/pattern binders
   named `alias` (Interface/TypeCheck/Checked.lean) no longer parse as bare
   identifiers. Escaped in place as `«alias»` (guillemet identifier) rather than
   renamed, so the field name — and therefore any `Repr`/derive output — is
   byte-identical. `alias?` binders and `"alias"` string literals are distinct
   tokens and were left untouched. No manifest change (the manifest references
   `alias` only in prose/variable names, never the field).

2. **`decreasing_by … omega` over-solves.** In `TypeCheck.lean` one termination
   proof (`checkMemberCallArgs`, ~line 7385) used `all_goals (simp_wf; omega)`;
   under v4.28.0 `simp_wf` already closes some goals, so `omega` errors with
   "No goals to be solved". Changed the lone bare `omega` to `try omega`
   (the file's other 20 termination proofs already used `try omega`).
   Termination proofs are irrelevant to the function's computational content.

3. **`to` is a reserved token in v4.28.0.** The hand-authored `openzeppelin-erc20`
   eval expression in `tests/forge-harness/manifest.json` bound a local
   `let to := 0xbeef` (a transfer-recipient address) and referenced it as
   `Value.word to`; `to` no longer parses as a bare identifier, so the generated
   `interpreter.lean` failed with `unexpected token 'to'` (the sole `lean=exit_1`
   in the first full replay). Alpha-renamed the local binder to `toAddr` in that
   one expression only (3 unique substrings). This is a local-variable rename
   inside a single eval; it changes no assertion and no expectation, and the
   manifest eval count is unchanged (420). The `"to"` strings that name the
   Solidity parameter live in generated AST-importer output, not the manifest,
   and were not touched.

## 2026-07-06 — Phase 1: Keccak byte-parity witness runs and passes

The `lean_exe keccakParity` (native-linked via the pinned `libleanffi`) compares
the repo-owned pure Keccak against the pinned FFI `ffi.KEC` on 11 representative
inputs (empty, real ABI selectors, event-topic signatures, and byte ranges
crossing the 136-byte rate boundary). `lake exe keccakParity` prints
`keccak parity: OK` and exits 0, discharging the roadmap's byte-parity
requirement directly rather than leaving it as an assumption.

## 2026-07-06 — Phase 2: shared package separates cleanly; no vendoring needed

The extraction closure is exactly the three files
`EvmCompiler/Simulation/{Interaction,OpenWorld,Outcome}.lean`. Their only imports
are the pinned `evmyul` package (`EvmYul.SharedState`, `EvmYul.StateOps`,
`EvmYul.Data.Stack`, `EvmYul.MachineStateOps`, `EvmYul.Operations`), Mathlib, and
each other — **no** other `EvmCompiler.*` module, and nothing Yul/EVM-semantics
shaped beyond what `evmyul` already provides. So the roadmap's entanglement
fallbacks (vendor-in-repo, or give up on the sibling) were not needed: a real
sibling package separates cleanly.

- Sibling repo created at `/Users/dan/Projects/evm-interaction` (own git repo,
  first commit), consumed here via `require «evm-interaction» from "../evm-interaction"`.
- The three files are byte-identical verbatim copies (same `EvmCompiler.Simulation.*`
  namespaces and declaration names), so evm-compiler's frozen theorem statements
  stay textually unchanged when it later adopts the package.
- All composition-critical vocabulary is present: `Interaction`/`Transcript`,
  `Query`/`Answer`/`ResourceQuery`, `ExternalRequest` + `Call/CreateRequest` +
  `Call/CreateResponse`, `OpenWorld` (+ `ofYulShared`/`ofEVMShared`), and
  `ForwardRel` with `strengthen_right`/`bind_right`/`mono`/`trans`
  (in `namespace …Simulation.Interaction.ForwardRel`).
- `ForwardRel` is nested under `namespace Interaction`, so its full name is
  `EvmCompiler.Simulation.Interaction.ForwardRel` (not `…Simulation.ForwardRel`);
  the bridge module aliases it accordingly.
- The sibling lakefile mirrors evm-compiler's `moreLeanArgs` (the same set of
  disabled linters) so the verbatim files compile under identical conditions.
- `scripts/check_shared_interaction_hashes.py` sha256-compares the sibling's
  three files against `../evm-compiler`'s live sources (read-only); it currently
  reports `shared_interaction_hashes=pass`. If the reference checkout is absent it
  reports `skip` rather than failing, so the check is enforceable in CI where the
  reference is present without blocking here when it is not.
- `SolidCore/Solidity/Interaction.lean` is the in-repo bridge: it imports the
  package and aliases `Interaction`/`Query`/`Answer`/`OpenWorld`/`ForwardRel`
  under `SolidCore.Solidity.Shared`. It is reachable from the `SolidCore.lean`
  root (so `lake build` verifies linkage) but not from the corpus build path, so
  Phase 2 is corpus-neutral (full replay green, cases=98, paired_cases_passed=yes).

## 2026-07-06 — Phase 3a: witness extraction is a clean verbatim move

No `open`/`variable`/`section` context existed at the `Examples` block sites, so
the blocks moved verbatim with only their enclosing namespaces reproduced. Import
edges are acyclic (Witness.Interface ← Witness.TypeCheck ← Witness.Checked,
mirroring the base modules). Manifest `lean.imports` gains `SolidCore.Witness.Checked`
per case (harness reads imports from the manifest, so nothing else changed).

## 2026-07-06 — Phase 3b: rename + AST split

- `SolidCore.Spine.L00_SourceSolidity` → `SolidCore.Solidity` everywhere,
  three-sided (6 Lean files, manifest's 1775 occurrences, and the 3 scripts'
  hardcoded namespaces/imports). No collision with the pre-existing
  `SolidCore.Solidity.Source.*` runtime layer (distinct sub-namespaces). The
  vestigial `SolidCore/Spine/` directory (and its stale READMEs describing the
  removed compiler-spine layout) is deleted; base modules moved to
  `SolidCore/Solidity/{Interface,TypeCheck,Checked}.lean`.
- The surface AST (the pre-`namespace Executable` section, ~430 lines: Literal,
  Expr, Stmt, FunctionDecl, SourceUnit, …) is split out into
  `SolidCore/Solidity/Ast.lean`; `Interface.lean` keeps `namespace Executable`
  (elaboration + the Phase-4-doomed observation layer) and imports Ast. Zero
  forward references from the AST section into `Executable`, so the split is at a
  clean namespace boundary. Verified end-to-end on one case via the harness
  (generator + manifest + eval), then full replay.

## 2026-07-06 — Phase 3d (evaluator consolidation) reordered after Phase 4

ROADMAP allows Phases 3 and 4 to interleave. Analysis of `Interpreter.lean`
showed the three older evaluator generations (`Expr.eval`,
`Expr.evalWithRuntime*`, `Expr.evalWithRuntimeOrderFuel*`) sit in mutual blocks
**separate** from the kept `evalWithRuntimeByContext`/`...Order` family, but their
remaining call sites are overwhelmingly inside `observe*` walker functions
(`observeShortCircuitEvaluation`, `observeTernaryEvaluation`,
`observeTryExternalCallEvaluation`, …) — which Phase 4 deletes — plus 3 sites in
`Stmt.eval` and 2 pure constant-eval sites in `Interface.lean`. Deleting the
observation layer first removes most of the old-evaluator references, making the
consolidation a small, low-risk port of the residual sites. So the order is:
3a, 3b, 3c, **Phase 4**, then 3d, then Phase 5.

## 2026-07-06 — Phase 3c: SharedSemantics folded into SolidCore.Solidity.Shared

SharedSemantics is a real, heavily-used dependency (Word/norm/Block/Call/Account/
Precompile/Log/External — 477 occurrences), not dead adapters. Folded it wholesale:
files moved to `SolidCore/Solidity/Shared/*.lean`, the namespace/module token
`SharedSemantics` → `SolidCore.Solidity.Shared` everywhere (all Lean files + the
manifest's 46 eval-expr occurrences), and the lakefile reduced to a single
`lean_lib SolidCore` (+ the keccakParity exe). The folded primitives share the
`SolidCore.Solidity.Shared` namespace with the interaction bridge's aliases with
no leaf collisions. Pure rename, no behavior change: build green + one
`Shared`-referencing case (`packed-storage`) passes end-to-end through the
harness. Its full-corpus validation is folded into Phase 4's replay (which builds
directly on this rename) rather than spending a separate ~20-min run on a
pure-rename step.

## 2026-07-06 — Run status and Phase 4 analysis (handoff point)

Completed, each green (full `compare_forge_solc_interpreter.sh` =
`forge_interpreter_compare=pass`, `cases=98`, `paired_cases_passed=yes`) and
committed:
- Phase 1 — substrate unification (Lean v4.28.0 + EVMYulLean @ 3c5c44a6).
- Phase 2 — shared `evm-interaction` package + hash-check.
- Phase 3a — witness corpus out to `SolidCore/Witness/`.
- Phase 3b — `Spine/L00_SourceSolidity` → `SolidCore.Solidity` rename + `Ast.lean`.
- Phase 3c — SharedSemantics folded into `SolidCore.Solidity.Shared`; single lib
  (validation bundled into the pending Phase 4 replay).

Phase 4 (delete observation layer) — analyzed, not yet executed. Findings that
make it safe and cheap to resume:
- The layer is **86 `*Observation` structures** (Interface 33, Interpreter 48,
  ABI 5) and **~215 `observe*` walkers** (Interface 75, Interpreter 118, ABI 22),
  interspersed with live code (not contiguous blocks).
- It is a **parallel reporting layer**: the ONLY live (non-`observe`, non-witness)
  caller of any `observe*` is `SharedPrimitiveRequest.eval`
  (`Interpreter.lean:2184`), which calls `context.observeLowLevelCallResolution`
  and `context.observeContractCreationResolution` **and takes only `.result`**.
  These two are dual-use (they compute the real low-level-call / creation result,
  not just report it) — exactly the roadmap's "changes what it computes" trap.
  Resolution: extract the `.result`-computing core of each into a plain function
  `SharedPrimitiveRequest.eval` calls, then delete the observation wrapper. (Note:
  these are the very choke points Phase 5 rewrites into `Query.external` /
  `Query`-create nodes, so the extracted cores feed directly into Phase 5.)
- **Do NOT delete** the storage-layout machinery (`StorageLayout`,
  `StorageLayoutCursor`, `slotSpan`, `Context.storageSlot?`, packing/path
  resolution) — it is core semantics Phase 5 depends on, not observation code.
- Manifest assertions referencing observations to reclassify (behavior →
  re-express against `CallResult`/`State`/logs and keep; record-structure-only →
  drop), recording each disposition in `docs/phase4-assertion-delta.md`:
  `arrayObservation`, `checkedBinaryArithmeticObservation`,
  `checkedTerminalEvaluationObservation`, `fixedObservation`, `pairObservation`,
  `scalarObservation`, `SourceUnitDeploymentAbiObservation` /
  `observeDeploymentAbiAtFrom`.

Phase 3d (evaluator consolidation) — analyzed; deferred until after Phase 4 (its
residual old-evaluator call sites are mostly inside `observe*` walkers). After
Phase 4, port the 3 `Stmt.eval` + 2 `Interface.lean` (pure constant-eval) sites
that use `Expr.eval`/`evalWithRuntime*` to `evalWithRuntimeByContext` and delete
the three now-dead mutual blocks (`Interpreter.lean` ~5024–7279).

Phase 5 (external world as the shared interaction monad) and Phase 6
(documentation/freeze) — not started; Phase 5 depends on Phases 2–4.

The repository is left green and committed at Phase 3c. `../evm-compiler` was
never modified. `../evm-interaction` was created and committed.

## 2026-07-06 — Phase 4 executed (observation layer deleted), green

Deleted all `*Observation` structures + `observe*` walkers (~294 declaration
blocks, ~12k lines) from `ABI.lean`/`Interface.lean`/`Interpreter.lean` and the
witness corpus. Method and lessons:

- **Declaration-level deletion, not line-range.** A parser removed whole
  top-level blocks whose name/text matched the observation pattern. No
  observation code was inside a *mixed* mutual block, so this was clean.
- **Pattern breadth matters.** The first pass required a word boundary after
  "Observation" and so missed `*ObservationStatus`/`*ObservationBoundary*` names
  and `.observe` (lowercase) methods; broadened to match "Observation" anywhere
  and `\.observe\b`.
- **Dual-use choke points.** `observeLowLevelCallResolution` /
  `observeContractCreationResolution` computed the real `.result` consumed by the
  live `SharedPrimitiveRequest.eval`; extracted plain
  `Context.lowLevelCallResult` / `Context.contractCreationResult` first (faithful
  copies of the `.result` match), then deleted the observe wrappers.
- **Dead-aggregator fallout.** Deleting observation defs orphaned 5 surviving
  witness aggregators that only combined them (`checkedSourceSolidityCoreSemanticsMatch`
  etc.). A transitive-broken sweep (delete surviving witness defs that reference a
  deleted name) removed exactly those 5, with a safety assert that no
  manifest-referenced def was caught. (Scoped to broken defs — did NOT garbage-
  collect the whole unreachable witness corpus, which stays in scope for the
  frozen regression suite.)
- **Manifest reclassification (420 → 419).** See `docs/phase4-assertion-delta.md`.
  The subtle one: 8 evals read the external-call transcript via
  `(CallResult.observe self).state.externalInteractions`. `externalInteractions`
  is a real `State` field and the deleted `State.observeEffects` copied it
  verbatim (no filtering by `self`), so this was faithfully re-expressed with a
  new plain accessor `CallResult.resultState : CallResult → State`. These are the
  very transcripts Phase 5 will formalize as the `Query` sequence.

Full corpus replay green: `forge_interpreter_compare=pass`, `cases=98`,
`paired_cases_passed=yes`. Storage-layout machinery untouched (Phase 5 needs it).

## 2026-07-06 — Phase 3d: evaluator consolidation (one expression evaluator)

A Fable review agent audited Phases 1–4 (confirmed the `resultState` and
choke-point extractions definitionally exact, zero dangling refs, all
manifest-referenced witnesses resolve) and **caught a plan error**: my earlier
handoff note said to delete `evalWithRuntimeOrderFuel`, but that is the *engine*
of the kept evaluator (`evalWithRuntimeByContext → evalWithRuntimeOrder →
evalWithRuntimeOrderFuel`). Deleting it would have broken the build. Corrected.

Consolidation executed:
- Ported the 5 remaining call sites off the old generations to
  `evalWithRuntimeByContext` (same `Except (Value × Runtime)` shape): the 3
  `value:`/`gas:` call-option sites in `Stmt.eval` (siblings already used
  ByContext — an unfinished migration) and the 2 pure constant-eval sites in
  `Interface.lean` (`Expr.evalLayoutBaseCore?` and `CoreExpr.evalWord?`, both over
  `Context.empty`/`State.empty`; projecting `.1` of the pair).
- Deleted the two dead old expression-evaluator families: gen-1
  (`Expr.eval`/`Expr.evalList` mutual) with its old `LValue.read/write/
  writeContainer/applyIncDec` + `LValues.writeTuple?` helpers (which called gen-1
  via `idx.eval` and had no kept callers), and gen-2 (`Expr.evalWithRuntime`/
  `evalListWithRuntime`/`memoryRefOrValueWithRuntime`/`resolveLValueWithRuntime`
  mutual). Kept: `Value.oneLike?` (used by the kept `ResolvedLValue.applyIncDec`),
  all `ResolvedLValue.*`, and the entire `...Order`/`...OrderFuel`/`...ByContext`
  engine. Build green confirms nothing kept referenced the deleted set.
- Per the roadmap, a divergence at the ported sites would be a latent bug to pin;
  the full replay is the arbiter (the call-option and erc7201-layout sites are the
  ones to watch). Result recorded on completion. **Replay green** (cases=98,
  paired_cases_passed=yes) — the ports are behavior-identical, no divergence.

## 2026-07-06 — Phase 5 scoping finding: storage is already word-addressed

Before starting the Phase 5 rewrite, confirmed the actual external-world shape,
which **de-risks the roadmap's central "snapshot problem"**:

- `State.storage : WordMap` where `WordMap := List (Word × Word)` — storage is
  **already word-addressed**, not typed. There is no `TypedStorage`/storage-tree
  representation anywhere. The `StorageLayout`/`Context.storageSlot?`/packing
  machinery *computes* which word slot a typed source access lands on during
  execution, but the stored state is words. So the OpenWorld word-storage
  snapshot is a near-direct read of `State.storage` (self account), and
  re-projection of `CallResponse.postWorld` back is trivial (words in, words
  out) — the roadmap's "layout encoding E has no computable inverse" concern is
  largely moot as the code stands. The fail-closed re-projection remains the
  right *policy* (an answered word not attributable to a touched slot is still a
  distinguished failure), but it is not blocked on inverting a typed encoding.
- The external-world environment lives in `Context` (Interpreter.lean 1487):
  `accountBalances`/`accountCodes`/`accountCodehashes : WordMap`/`ByteMap`,
  `contractAddresses`/`contractCreationCodes`/`contractRuntimeCodes` (named maps),
  block/tx env, `gasleft`. These become the `OpenWorld`-shaped environment read
  as state (no query), post-answer replaced by `postWorld`.
- The oracle-record fields Phase 5 deletes are exactly
  `Context.lowLevelCallResults : List LowLevelCallResult` and
  `contractCreationResults : List ContractCreationResult` — the tables that
  `Context.lowLevelCallResult`/`contractCreationResult` (the Phase-4 choke-point
  functions) read. Those two functions are precisely where `Query.external` node
  emission goes.
- Type bridging needed at the boundary: interpreter `Word` (Nat) ↔ shared
  `EvmYul.UInt256` (Fin); interpreter `List Byte` calldata/output ↔ shared
  `ByteArray`. Both are total conversions.

Implication: Phase 5 is still a real monadic rewrite (thread `Interaction`
through the `Expr`/`Stmt` mutual block so the two choke-point functions emit
`Query.external` and resume on `Call/CreateResponse`), but the snapshot/
re-projection machinery is far cheaper than the roadmap's worst case.

## 2026-07-06 — Phase 5 prep: corrected choke points; dead cluster removed; rewrite is mechanical

Two corrections/findings while starting the rewrite:

- **The real choke points are NOT the ones Phase 4 refactored.**
  `SharedPrimitiveRequest`/`SharedPrimitiveResult`/`SharedPrimitiveRequest.eval`
  (and therefore the Phase-4-extracted `Context.lowLevelCallResult`/
  `contractCreationResult`) were **dead** — unreferenced anywhere in the repo.
  The Phase-4 refactor was still behavior-preserving (it faithfully transformed
  dead code), but the earlier "choke point" identification (mine and the review
  agent's) was wrong. The **live** external-effect sites are
  `Context.resolveLowLevelCall` (Interpreter.lean ~1708) and
  `Context.resolveContractCreation` (~1724), consumed synchronously inside
  `Expr.evalWithRuntimeOrderFuel` (sites ~5345/5362, ~6929, ~7016). Each reads the
  oracle table (`context.lowLevelCallResults`/`contractCreationResults`) inline,
  returns a `LowLevelCallResult`/`ContractCreationResult`, and records the effect
  via `runtime.recordExternalInteraction` into `state.externalInteractions`.
  Deleted the entire dead `SharedPrimitiveRequest` cluster (~63 lines); build
  green (dead code, so corpus-neutral — validation folds into the sub-step-1
  checkpoint).

- **The rewrite is mechanical, not a from-scratch monad plumb.** The shared
  `Interaction Error` already has `Monad` and `MonadExceptOf Error` instances
  (evm-interaction `Interaction.lean` 785/790). The evaluator today is effectively
  `Interaction` with only `done` leaves (it returns `Except RevertData (Value ×
  Runtime)`). So the conversion is: change the return type to
  `Interaction SolidityFailure (Value × Runtime)`; `Except.ok x → pure x`,
  `Except.error e → throw (…revert e)`; the `fuel = 0 → Except.error` arm →
  `throw …outOfFuel` (the distinguished fuel-exhaustion failure the roadmap
  wants); and at the ~4 live sites emit `Query.external world (CallRequest/…)` and
  resume on `Call/CreateResponse` (sub-step 1: answered from the Context
  environment so fixtures run unchanged). `do`-notation carries over via the Monad
  instance. The change is pervasive (every `Except.ok`/`error` and result-match in
  the mutual block, then propagation through `Stmt.eval`/`Contract.call`/
  `callTransaction`/ABI entries, with `?`-named Option adapters kept for the
  manifest through sub-step (2)), but each edit is mechanical.
