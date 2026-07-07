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
  `Except.error e → throw (…revert e)`; the expression evaluator's `fuel = 0` arm stays a
  `.revert typeMismatch` (behavior-preserving); `outOfFuel` is reserved for the
  future `Stmt.eval`-level truncation the roadmap wants; and at the ~4 live sites emit `Query.external world (CallRequest/…)` and
  resume on `Call/CreateResponse` (sub-step 1: answered from the Context
  environment so fixtures run unchanged). `do`-notation carries over via the Monad
  instance. The change is pervasive (every `Except.ok`/`error` and result-match in
  the mutual block, then propagation through `Stmt.eval`/`Contract.call`/
  `callTransaction`/ABI entries, with `?`-named Option adapters kept for the
  manifest through sub-step (2)), but each edit is mechanical.

## 2026-07-06 — Phase 5 foundation landed (green)

Built and proved the shared-alphabet foundation in `Interpreter.lean` (additive,
build green, corpus-neutral — validation folds into the sub-step-1 checkpoint):

- `SolidityFailure` (revert | outOfFuel) and `abbrev SolI := Interaction
  SolidityFailure` — the interaction monad the external boundary emits into.
- Total bridges: `wordToU256`/`u256ToWord`, `bytesToByteArray`/`byteArrayToBytes`,
  `wordToAddress`/`addressToWord`, `lowLevelKindToCallKind`/`callKindToLowLevel`.
- `buildCallRequest` (fills `requestedGas` from `{gas:}` else ambient `gasleft`)
  and `decodeCallResponse`.
- `emitLowLevelCall`: emits `Query.external default (.call request)` and resumes on
  the `CallResponse` (checkpoint-1: world snapshot is placeholder `default`).
- `answerCall`/`contextAnswer`: replay-from-Context answerer (gas-lenient — try
  the oracle without gas, else the sent `requestedGas`). `SolI.runFromContext`
  folds the tree (fuel-bounded); `SolI.queryTranscript` exposes the query sequence.
- `phase5DemoTree`: a two-external-call interaction tree. Verified end-to-end —
  `phase5DemoTranscriptLength Context.empty = 2`; `runFromContext` folds it to
  `some [false, false]` against the empty oracle (fail-closed); transcript length
  2. This is the Phase 5 acceptance "demo witness shows a two-call execution as an
  explicit Interaction tree with its query transcript" in foundation form.

Remaining Phase 5 work is the evaluator wiring: change `Expr.evalWithRuntimeOrderFuel`
(+ mutual companions, `Stmt.eval`, `FunctionDef.call?`, `Contract.call?`/
`callTransaction?`) return types to `SolI`; replace the synchronous
`resolveLowLevelCall`/`resolveContractCreation` reads (Interpreter.lean
~5345/5362/6929/7016) with `emitLowLevelCall`/an `emitContractCreation` analog;
keep `?`-named Option adapters (via `SolI.runFromContext`) for the manifest; then
sub-steps (2) scripted responders and (3) delete the oracle `Context` fields.

## 2026-07-06 — Phase 5 sub-step-1a: expression evaluator emits Query.external (green)

Converted the expression evaluator's return type `Except RevertData (Value ×
Runtime)` → `SolI (Value × Runtime)` across the `...OrderFuel` mutual block, the
`...Order` wrappers, and the `evalReturn*Order` family. Mechanical: `Except.ok →
pure`, `Except.error e → throw <| SolidityFailure.revert e`, aided by
`instance : MonadLift (Except RevertData) SolI` (pure helpers auto-lift in
do-blocks). The 2 live low-level-call sites now `emitLowLevelCall` (emitting a
`Query.external default (.call request)` node) instead of a synchronous
`resolveLowLevelCall`. The `...ByContext` functions (the boundary `Stmt.eval`
matches on) stay `Except`-returning and fold the SolI tree via `SolI.foldExpr fuel
context` (= `runFromContext` then `.revert e → .error e`, `.outOfFuel →
typeMismatch`), with `fuel = orderFuel expr + 1`.

A Fable review of this increment: **fuel bound verified safe** (query count ≤
syntactic `Expr.lowLevelCall` node count ≤ `orderFuel`, since `Expr` has no
repetition constructs — loops/internal calls are in `Stmt`, re-folded per use — so
`.outOfFuel` is unreachable; my earlier "steps ≤ fuel" framing was wrong but the
syntactic-count argument holds); `decodeCallResponse` verified faithful
(success/output exact modulo the norm the oracle already applies). Two dormant
bugs it caught, both fixed before commit:
- `callKindToLowLevel .callcode` mapped to `.call` (would misroute callcode oracle
  keys under scripted responders) → now maps to `.callcode`.
- `answerCall` gas ordering: tried the `gas?=none` oracle row first for every
  request, which could shadow an exact `gas?=some g` row → now exact-gas-first
  (`some requestedGas`), then no-gas resolution.
Correction to the earlier "prep" note: the evaluator's `fuel = 0` arm stays
`.revert typeMismatch` (behavior-preserving); `outOfFuel` is reserved for the
future `Stmt.eval`-level truncation.

**Not yet converted (recorded residue, sub-step-1b):** a third live external site
in `Stmt.eval` (high-level call / try-catch path, ~7041) and the 2 contract-create
sites (~5493/5513, still reading `lookupContractCreation?`). Creates are soluble in
the shared alphabet via `initCode := creationCode ++ constructorArgs` (responder
recovers the name by prefix-match) — no shared-type change needed. Sub-step (3)
(delete oracle `Context` fields) is gated on converting all three.

Full corpus replay green: `forge_interpreter_compare=pass`, `cases=98`,
`paired_cases_passed=yes`.

## 2026-07-06 — Dev-loop smoke replay added

`scripts/smoke_replay.sh`: a curated ~29-case subset run Lean-only
(`--skip-forge`) for the edit/build/check dev loop; the full replay stays the
commit gate. Rationale: only the Lean interpreter changes during development, so
re-running Forge (per-case solc-compile + Foundry-EVM run, the dominant cost) is
waste — `--skip-forge` still generates each witness from the solc AST and
validates the Lean `#eval`s return `true`, catching any Lean regression. The set
covers the full Phase 5 external-effect surface plus broad
evaluator/statement/storage/reference/ABI/event sentinels, excluding the
minute-plus heavy contracts (erc721-royalty, erc1155-supply variants, checkpoints,
uniswap-v3-math, frontend-frontier) which run only in the full replay.
`SMOKE_WITH_FORGE=1` re-enables Forge for the subset.

## 2026-07-06 — Replay parallelism (`--jobs`), ~2.8× faster dev loop

Diagnosed replay slowness by measurement: per case ≈ 0.07s solc-AST-import +
~4s fixed `SolidCore` olean load + variable `#eval` (heavy OZ contracts run a
minute+ in the pure-Lean interpreter). The harness ran cases **sequentially on 1
of 14 cores**. Sequential smoke (28 cases, Lean-only) = **770s**.

Added an opt-in `--jobs N` flag to `scripts/run_forge_interpreter_harness.py`
(default `1` = byte-identical to the original sequential loop, so the official
full-replay gate command is unchanged). Cases run in a `ThreadPoolExecutor`;
per-case stdout is captured via a **thread-routing stdout** (a proxy that sends
writes to the current thread's buffer, else the real stdout) and replayed in
manifest order. (First attempt used `contextlib.redirect_stdout`, which swaps the
process-global `sys.stdout` and corrupted capture across threads — only 1 of 28
case lines survived; the thread-local router fixes it. Verified `--jobs 5`
emits all cases in manifest order with the correct pass summary.)

`smoke_replay.sh` now passes `--jobs 10` (override `SMOKE_JOBS`): smoke ≈ **272s**
(2.8× — the floor is the single longest heavy case, not the 10× core count).
Dropped `solmate-erc20` from the smoke set (redundant with `openzeppelin-erc20`).
The `--jobs` flag also speeds the full replay (~20 min → a few min) when opted in;
the commit gate keeps the default sequential command.

## 2026-07-06 — Phase 5 stage 0: repair library build left red by sub-step-1a

A Fable agent designing the Phase 5 propagation plan (`docs/phase5-propagation-plan.md`)
found that `lake build SolidCore` was **red at HEAD** (commit a6d3f7d): two
witnesses in `SolidCore/Witness/Interface.lean` (`unspecifiedBinaryOrderEval`,
`unspecifiedTupleOrderEval`, ~20834/20893) still matched `Except.ok` against
`Expr.evalBinaryWithRuntimeOrder`/`evalWithRuntimeOrder`, which sub-step-1a
changed to return `SolI`. **The replay harness generates per-case witness files
and never builds `SolidCore.Witness.*`, so sub-step-1a's green replay did not
catch the library break.** This is a process gap: a green replay ≠ a green
`lake build`.

Fix (validated): wrap both scrutinees in `SolI.foldExpr (Expr.orderFuel core + 1)
unspecifiedBinaryOrderContext (…)` exactly as the `…ByContext` adapters do; the
match arms stay byte-identical. Both witnesses still `#eval` to `some true`
(constant-eval, empty state — the fold answers no queries, so behavior is
identical); they are not referenced by the manifest. `lake build SolidCore` green.

Hardening: `scripts/smoke_replay.sh` now runs `lake build SolidCore` first, so a
library/witness break can never again hide behind a green replay. The Phase 5
propagation plan (model A refined; 8 buildable stages; build-validated PoC) is
committed as the roadmap for the remaining work.

## 2026-07-06 — Phase 5 stage 1: thread `SolI` through `Stmt.eval` + call chain

Executed stage 1 of `docs/phase5-propagation-plan.md` (model A refined). The
statement evaluator and function/contract call chain now produce a propagating
`Interaction` tree; a single top-level adapter folds it back to
`Option`/`Except`.

- Added `SolI.run` (fuel-free structural fold over `Interaction`, answering each
  query from `Context` via `contextAnswer`) and `SolI.caught` (reifies a
  throw-revert Expr tree's revert leaf into an `Except RevertData` value while
  re-throwing `outOfFuel`). `caught` is the ONLY `tryCatch` in the interpreter.
- `LValue.resolveWithRuntime` and `LValues.writeTupleWithRuntime` (renamed from
  `writeTupleWithRuntime?`) now return `SolI`.
- The whole `Stmt.eval`/`evalList`/`evalWhile`/`evalDoWhile`/`evalFor` mutual
  block returns `SolI Result`. The four `fuel = 0 → none` arms became
  `throw SolidityFailure.outOfFuel` (the only throw that escapes `Stmt.eval`);
  recursive `some/none` matches became do-binds; `…ByContext` scrutinees became
  `← (…WithRuntimeOrder tree).caught`; the 9 resolve/writeTuple sites became
  `← (…).caught`.
- `Stmt.tryExternalCall`/`tryContractCreate` kept their `…ByContext`/oracle
  reads synchronous (that is stage 1b/1c); only their Option/Except plumbing was
  threaded (leaves `some → pure`, the four recursive `Stmt.eval` sites do-bind).
- `FunctionDef.evalBodyEntry` : `Option (SolI Result)`, `FunctionDef.call` :
  `Option (SolI CallResult)`, and `Contract.call`/`Contract.callTransaction` :
  `Option (SolI CallResult)`. The frozen `?`-named adapters (`FunctionDef.call?`,
  `Contract.call?`, `Contract.callTransaction?`) keep their exact signatures and
  fold via `SolI.run`, so the manifest, ABI.lean, Checked.lean, and Context stay
  unchanged. `FunctionDef.call?_reverted_rolls_back` was restated against the
  tree (`= pure (Result.reverted …)`) and reproved with the extended simp set.

Why behavior-preserving: `contextAnswer` is a pure function of `Context`, so
answering a query at the per-call fold (now) or the per-expression fold (before)
yields identical answers; the only delta is `fuel = 0` propagation, invisible
through the `Option`/`Except` adapters. Full `lake build SolidCore` and
`scripts/smoke_replay.sh` (28 cases, `forge_interpreter_compare=pass`) are green.

Scope deviation (necessary for a green library build): besides
`SolidCore/Solidity/Interpreter.lean`, three direct `Stmt.eval` callers outside
the plan's type table had to be adapted to the new tree type, each a minimal
signature-preserving fold at the boundary (`(SolI.run ctx …).toOption`):
`Stmt.eval?` in `SolidCore/Solidity/Interface.lean` (a frozen witness-facing
`?`-adapter) and two hand-written witness helpers in
`SolidCore/Witness/Interface.lean` (`abiEncodeCoreExprResult`,
`unspecifiedTupleOrderStmtEval`). No fixtures, manifest, ABI.lean, Checked.lean,
TypeCheck.lean, or Context were touched.

## 2026-07-06 — Phase 5 stage 1b: high-level external-call site emits

`Stmt.tryExternalCall`'s remaining synchronous `context.resolveLowLevelCall`
became `← emitLowLevelCall context kind target calldata value gas?`, matching the
two Expr-evaluator sites. The `missingCode` extcodesize guard (a state read, no
query) stays *before* the emit; `recordExternalInteraction` keeps consuming the
decoded result. The high-level external-call / try-catch transcript is now real.
Behavior-preserving (`contextAnswer` answers from the same oracle). Build + smoke
(28 cases, `forge_interpreter_compare=pass`) green.

Extends R7 (gas-key erasure): the high-level call site now shares the sub-step-1a
no-gas vs `{gas: gasleft}` transcript ambiguity — a recorded, deferred `gasleft`
limitation, no new mechanism.

## 2026-07-06 — Phase 5 stage 1c: contract creation emits (name-encoded initCode)

Creates now emit `Query.external default (.create request)`. The source semantics
creates by contract *name* (pre-compilation; fixtures key the oracle by name and
do not populate `contractCreationCodes`), so identity is encoded canonically:
`creationInitCode name args` = 32-byte big-endian UTF-8-name-length ‖ name bytes ‖
args (injective); `decodeCreationInitCode?` inverts it fail-closed (length
overrun or non-UTF-8 → `none`).

- `buildCreateRequest`: `kind := .create2` iff a salt is present, else `.create`;
  `creator := wordToAddress context.self`; `value`; `initCode := creationInitCode`;
  `salt := salt?.map wordToU256`; `permission := true`.
- `emitContractCreation : … → SolI ContractCreationResult`. `CreateResponse` has
  **no `success` field**, so `decodeCreateResponse` sets `success := address ≠ 0`
  (EVM convention); name/args/value/salt are carried through for oracle keying and
  `recordExternalInteraction`, mirroring `decodeCallResponse`.
- `answerCreate` decodes the name from `initCode`, calls `lookupContractCreation?`
  (no keying reimplementation) else `ContractCreationResult.failedRequest`, and
  encodes back with `address := if success then address else 0`. The `.create` arm
  was added to both `contextAnswer` and `SolI.runFromContext`.
- The 3 sites converted: two `Expr.contractCreate` (salt-less and salted) and
  `Stmt.tryContractCreate`. Failure branches stay equivalent —
  `RevertData.fromRawBytes [] = RevertData.empty`, so the Expr sites' old explicit
  `none → RevertData.empty` branch collapses into `¬success → fromRawBytes output`;
  `resolveContractCreation`'s `none → failedRequest` matched `answerCreate` exactly
  at the Stmt site.

Deferred limitation recorded here and in `ROADMAP.md`'s gap registry: the emitted
`initCode` is source-canonical, not compiled creation bytecode — a transcript-level
mismatch analogous to `gasleft` erasure, resolved at the future lowering.

Build + smoke green.

## 2026-07-06 — Phase 5 stage 1d: precompile builtins emit (open-world staticcalls)

`ecrecover`/`sha256`/`ripemd160` are, in the EVM, a `STATICCALL` to address
1/2/3 — ordinary external calls, not a residue family. Their evaluator sites now
emit `Query.external default (.call request)` via a new `emitPrecompileWord`
helper (`kind := .staticcall`, `recipient/codeAddress := Precompile.address kind`,
`calldata := input`, `value := 0`, `gas? := none`), decoding the output word with
`Precompile.outputWord?` — exactly what `lookupPrecompileOutputWord?` did inline.
`keccak256` is the KECCAK256 opcode (computed in-EVM), so it stays local — no
query.

The result is computed **in the responder**: `answerCall` already reaches these
rows — `LowLevelCallResult` and `Precompile.Result` are the same type
(`Call.Result ExternalCallKind`), and `answerCall → lookupLowLevelCall? →
Call.Result.lookup? context.lowLevelCallResults` reads the very rows
`Precompile.lookup?` keyed (kind=staticcall, target=address, calldata=input,
value=0, gas?=none), resolved through the existing exact-gas-first-then-no-gas
fallback. No `answerCall` extension and no fixture-row change were needed.

The two converted sites (`Expr.externalHash`, `Expr.ecrecover`) leave
`Context.ecrecoverAt`, `ExternalHashKind.lookup?`, `lookupPrecompileOutputWord?`,
and `lookupPrecompileCall?` unused on the execution path; they still read
`context.lowLevelCallResults` and are deleted at stage 3 with the oracle fields.
Required before stage 3 (they blocked deleting the field) and for the eventual
ForwardRel composition (the Yul side emits these precompile staticcalls).

Build + smoke green.

## 2026-07-06 — Precompiles: match evm-compiler exactly (no special Solidity handling)

Directive: precompiles should be treated exactly as evm-compiler's Yul/EVM
interaction semantics treat them — as ordinary external calls, emit-and-
environment-answer, with NO precompile-address special-casing in the semantics.
Confirmed evm-compiler's model: `EvmCompiler/Yul/InteractionSemantics.lean:129`
turns a CALL into `.request (.external world (.call request))` with zero
precompile logic anywhere in its Simulation/Yul interaction layer.

Current state after stage 1d (`eb60734`): the *emit* side already matches
(`ecrecover`/`sha256`/`ripemd160` source builtins emit a staticcall to address
1/2/3; ecdsa case passes `forge=ok lean=ok`). The residual "special stuff" to
remove, folded into **Stage 2 (scripted responders)** where the answer path is
reworked:
- `Context.lookupLowLevelCall?`'s `builtinStaticcallResult?` fallback (computes
  identity 0x4 / modexp 0x5 in the semantics) — remove; precompiles answered
  uniformly from the responder like any external call. No corpus case exercises
  identity/modexp, so this is corpus-safe.
- `emitPrecompileWord` — unify into the ordinary external-call emit
  (`buildCallRequest`/`emitLowLevelCall`); the only legitimately Solidity-specific
  part is recognizing the builtin *name* (`ecrecover`/`sha256`/`ripemd160`),
  since Yul has no such builtins.
- `SolidCore/Solidity/Shared/Precompile.lean` computation — remove from the
  semantics (the open-world environment owns precompile results). Keep only the
  address constants needed to build the staticcall target.

## 2026-07-06 — Phase 5 stage 2: scripted responders + precompile alignment + kind-dependent call requests

Landed the stage-2 machinery. Manifest UNCHANGED (R5): the responder conversion
of the manifest is deferred to stage 3; stage 2 adds the machinery and validates
equivalence out-of-band.

**Scripted responder (`SolI.runWith`, fail-closed).** `ScriptedResponder :=
List OracleRow` (`OracleRow.call LowLevelCallResult | .create ContractCreationResult`).
`SolI.runWith` folds a tree structurally (no fuel, like `SolI.run`), answering
external call/create queries from the responder rows and **failing closed** on a
total miss (`ResponderFailure.unmatched request`, carrying the request for a
diff) instead of the old fail-open `failedRequest`. `ScriptedResponder.ofContext`
derives the responder mechanically from a `Context`'s oracle fields. Matching
mirrors `answerCall`/`answerCreate` keying **exactly** (target recovered from
`codeAddress`; exact-gas-first then no-gas; create name/args/value/salt from the
name-encoded initCode, fail-closed on malformed), so on any tree whose external
requests all have a matching row the responder answers identically to
`contextAnswer`.

Design note — **find-first, not strict-ordered.** The plan floated an
order-consuming responder (out-of-order ⇒ failure). We match `List.find?`-first
(same as the retired `contextAnswer`) to *guarantee* behavioral equivalence:
several fixtures list duplicate-key rows (e.g. uniswap
`importedSafeTransferFromRejectsFalseAndFailedCall`) whose order a consuming
responder would diverge on. The substantive win — a loud failure on any external
request the fixture did not anticipate — is retained via fail-closed-on-miss.

**Fail-open reliance: NONE.** Enumerated every intentional-failure witness in the
corpus; all supply an explicit `success := false` row (uniswap failed-call,
vesting/refund-escrow/payment-splitter rollbacks, multicall delegatecall
failure). The one call-with-no-row case (dapphub-weth9 second withdraw) reverts
on a `require` guard *before* issuing the call, so it never reaches the fail-open
path. No positive assertion in the 98-case corpus exercises the fail-open miss,
so making the responder fail-closed changes no expectation.

**Precompile alignment (match evm-compiler).** Removed
`Context.lookupLowLevelCall?`'s `builtinStaticcallResult?` fallback and deleted
the in-semantics identity/modexp computation from `Shared/Precompile.lean`
(`successfulStaticcall`/`identityStaticcall`/`expMod`/`expModAux`/`modexpOutput`/
`modexpStaticcall`/`builtinStaticcallResult?`). `modexpInput` (calldata encoding,
not computation) stays. Precompiles are now ordinary external calls answered by
the environment/responder — no special-casing in the semantics. Corpus-safe: no
case computes identity/modexp; the two now-unasserted `checked{Identity,Modexp}
PrecompileStaticcallMatches` witness defs are dead (not referenced by manifest or
any `#eval`/theorem). `keccak256` stays local (opcode).

**Kind-dependent `buildCallRequest` (+ `answerCall` inversion).** delegatecall:
`recipient := self`, `transferValue := 0`, `apparentValue := context.value`;
staticcall: `transferValue := 0`; call/callcode unchanged. `codeAddress := target`
for every kind, and `answerCall`/`ScriptedResponder.answerCall?` recover the
callee from `codeAddress` (not `recipient`) so the oracle round-trips for
delegatecall (whose recipient is now the caller). All corpus delegatecall/
staticcall rows carry `value = 0`, so the round-trip is exact.

**Validation (the stage-2 gate).** `scripts/check_responder_equivalence.py`
regenerates every oracle-bearing witness (40 evals across 18 cases) with each
tree-folding checked entry name-swapped to its `*RespCheck` twin (fold under
`ScriptedResponder.ofContext` instead of `contextAnswer`) and asserts each still
prints the case's expected value — equivalence of results AND the recorded
external-interaction transcripts the assertions check. Result:
`responder_equivalence_check=pass`, `oracle_cases=18 equivalent=18`. Plus
`lake build SolidCore` + smoke (28 cases, `forge_interpreter_compare=pass`).

## 2026-07-06 — Phase 5 stage 3: oracle Context fields deleted; manifest + witnesses fold under scripted responders

The fixture oracle left `Context`. `Context.lowLevelCallResults`/
`contractCreationResults` are gone (fields, both initializers), together with
every reader: `lookupLowLevelCall?`, `resolveLowLevelCall`,
`lookupContractCreation?`, `resolveContractCreation`, `lookupPrecompileCall?`,
`lookupPrecompileOutputWord?`, `Context.ecrecoverAt`, `ExternalHashKind.lookup?`,
`answerCall`, `answerCreate`, and `ScriptedResponder.ofContext`. In
`Shared/Precompile.lean` the row-lookup family (`request`/`callKind`/`lookup?`/
`lookupOutputWord?`/`ecrecover?`/`ecrecoverAt`) is deleted; only `address`,
`ecrecoverInput`, `outputWord?`, `modexpInput` (encodings, not lookups) remain.

**`contextAnswer` collapses to `Query.defaultAnswer`.** `defaultAnswer`'s
call/create shapes decode to exactly the old fail-open `failedRequest`
(success = false / address = 0, empty output), and `decodeCallResponse`/
`decodeCreateResponse` rebuild results from the original emit params — so the
frozen `?` adapters are bit-identical on the row-less contexts that remain.
`SolI.runFromContext` likewise answers everything with `defaultAnswer` (kept
fuel-bounded for `foldExpr`/transcript utilities).

**Two responder folds, by design:**
- Corpus manifest: fail-closed `SolI.runWith` via `*UnderResponder` wrappers
  (responder right after fuel). All 40 oracle evals across 18 cases converted;
  rows moved verbatim from context literals into `responderOfResults` args;
  eval count unchanged (419). Direct-literal sites, let-bound-context sites
  (every consuming entry of the context var swapped), and locally-bound `call`/
  `construct`/`wordOk` lambdas (responder threaded as a lambda parameter,
  row-less sites pass `[]`) — validated by the stage-2 equivalence check
  re-run just before the flip (18/18); the full replay gates the follow-up entry.
- Witness sentinels: fail-open `SolI.runFailOpen` via `*FailOpen` twins — rows
  answer find-first with the retired `contextAnswer`'s exact keying; misses take
  `defaultAnswer` (≡ the old fail-open `failedRequest`). Several sentinels
  deliberately exercise the miss path (`lowLevelCallGasMismatchReturnsFalse`,
  `externalFunctionPointerTryCatchCatchMatches`, …), so fail-open preserves
  every recorded truth value by construction; verified — 138 witness evals
  byte-identical to the pre-stage-3 baseline (including three pre-existing
  `some false` and one `none`).

Stage-2 scaffolding removed with the fields: the `*RespCheck` twins and
`scripts/check_responder_equivalence.py` (its job — proving responder ≡ context
answers on the corpus — was done; final run 18/18 pass).

Zero `lowLevelCallResults`/`contractCreationResults` references remain in
SolidCore/, scripts/, tests/. Gates: build green; smoke 28 cases pass (+ the two
oracle cases outside the smoke set, `openzeppelin-ecdsa` and
`typechecker-calldata-origins`, pass via `--only`); witness baseline identical;
the full sequential 98-case replay + AST audit gate run was IN PROGRESS at
commit time (committed early at the user's request, on the strength of
build/smoke/equivalence/baseline gates and an independent review of the diff);
its result and wall-clock are recorded in a follow-up entry.

## 2026-07-06 — Phase 5 stage 3 follow-up: full-gate results

The gates left in progress at the stage-3 commit (`49a20f3`) both passed
against that exact tree:

- **Full corpus replay**: `forge_interpreter_compare=pass`, `cases=98`,
  `paired_cases_passed=yes`, zero case failures. Run with `--jobs 10`
  (~16 min wall-clock; a first sequential attempt was killed by the session's
  background-task reaper at 74/98 after ~60 min — nothing about the corpus).
- **AST frontend audit**: `rendered_sources=97`, `render_failures=0`,
  `unknown_source_scalar_value_fields=0` (no unimplemented constructs).

With these, the complete stage-3 gate battery is green: build (1091 jobs),
smoke (28 cases) + the two oracle cases outside the smoke set via `--only`,
witness truth-value baseline (138 evals byte-identical), stage-2 responder
equivalence re-run just before the flip (18/18), full replay, and AST audit.
## 2026-07-06 — Lowering-prep cleanup pass (N1/N2/N4 from the readiness study)

Executed on branch `cleanup/lowering-prep` (worktree, based at 56f59fa), per
`docs/compile-to-yul-readiness.md` §5's "do now" list. Every "zero uses" claim
was re-verified against the current tree (post-Phase-5-stage-3) before any
deletion, since the study predates the stage-1e/2/3 commits.

- **N1 — landed.** Deleted the 18 dead observation-era classifier enums from
  `Interpreter.lean` (`LowLevelCallEvaluationStatus` … `CallExitMode`; full
  list in the commit). Re-verification: rg across `SolidCore/`,
  `tests/forge-harness/manifest.json`, `scripts/` found zero references
  outside the inductive declarations themselves (type names and all
  constructors). Interspersed live types (`TernaryBranch`,
  `RevertPayloadSource`, `RequireCheckSource`, `TryCatchMatchKind`,
  `SwitchBranchSelection`) kept.
- **N2 — SKIPPED: the readiness doc's dead-code claim is stale.** The doc
  says the `Runtime` byte-memory shadow (`memoryByteMap`/`memoryBytesUsed`/
  `memoryFreePointer`/`memoryAllocations`, readers `loadMemoryByte?`/
  `readMemoryBytes?`) is "written only at newBytes/newDynamicArray and read
  nowhere". On the current tree it has a live reader: the witness
  `memoryAllocationFootprintMatches` (+ 4 helper defs,
  `SolidCore/Witness/Interface.lean:1600–1661`) asserts on all four fields
  and both readers. Nothing *semantic* reads the shadow, so retiring it is
  still right eventually — but it now requires deleting witness defs in the
  same witness territory the concurrent main-tree agent's final Phase-5 work
  touches (the reason N3 was deferred), so it is skipped here rather than
  half-done. Revisit after Phase 5 merges, together with N3.
- **N3 — deferred by instruction**, not attempted: the in-file example defs at
  the tail of `Interpreter.lean` are inside the main-tree agent's uncommitted
  final work; moving them in parallel guarantees conflicts.
- **N4 — landed.** `Ast.lean` no longer imports `SolidCore.Solidity.ABI`.
  The dependency turned out to be **entirely vestigial for Ast itself**: the
  surface AST uses no ABI/Interpreter/Keccak name (it builds unchanged
  without the import; `Word`/`Byte` are local abbrevs over
  `Shared.Word`/`Nat`). The real consumer was `Interface.lean`, which
  imported only `Ast` and received ABI/Interpreter/Keccak transitively; it
  now imports `SolidCore.Solidity.ABI` explicitly. No import cycle
  (ABI → Interpreter/Keccak/Word; Ast → Shared only), no declaration renamed,
  manifest untouched.
- **Doc corrections** (same pass): fixed the readiness doc's Sm seam note —
  the free-memory pointer *lives at* `0x40` and initially *points to* `0x80`;
  softened `function-boundary-refactor-plan.md` §1.5's "solc inlines
  modifiers" to the accurate split: the *semantics* is placeholder
  substitution; legacy codegen inlines, via-IR may emit modifier inner bodies
  as per-layer Yul functions (an emission choice, not a semantic one).
- **ROADMAP**: added the recursion/internal-call acceptance gap to the known
  semantic gaps registry (internal-linkage calls inlined with fuel 64;
  recursion/deep nesting silently rejected at elaboration while solc
  accepts; status "Deferred — plan exists",
  `docs/function-boundary-refactor-plan.md`).

Gates per landed item: `lake build SolidCore` + `scripts/smoke_replay.sh`
(28 cases, `forge_interpreter_compare=pass`, all `lean=ok`).
## 2026-07-06 — A1 rational constants: over-reject (completeness) fix, no unsoundness

The audit (`docs/rational-constants-audit.md`, commit `5c26c24`) corrected the gap
registry's suspicion. A1 was recorded as **suspected unsoundness** ("may currently
mis-evaluate"). It is not: a `NumberRat` exact-rational folder already existed
(Phase 3b), folds in unbounded-precision ℚ, and gates integer-only results on
exact division — **0 WRONG-VALUE divergences** across the whole probe set. The
classic truncation traps (`7/2*2`, `1/2 + 1/2`) already return solc's exact `7`
and `1`, not `6`/`0`.

The real, live gap was **OVER-REJECTION** (a completeness gap): `NumberRat` was
over `Nat`, so any constant whose folded value is negative — formed by subtraction
or a nested unary minus — was rejected even though solc accepts it. Confirmed on
three probes: `int256 = 0 - 5` (−5), `int256 = 3 - 10` (−7),
`int256 = 7 / 2 * 2 - 100` (−93, a negative fractional intermediate).

**The fix (engine):** widen `NumberRat` to a signed exact rational
(`num : Int`, `den : Nat` strictly positive; `mk?` canonicalizes the sign onto
the numerator). Consequences:

- `NumberRat.sub` is now **total** (`some (lhs.sub rhs)` in
  `BinaryOp.applyNumberRat?`) — a negative result is representable. This is the
  whole fix for the three over-rejects.
- `div?` routes the (possibly signed) denominator through `mk?`; `pow` over
  signed `Int` handles negative bases for free.
- New `NumberRat.exactInt? : Option Int`; `exactNat?` is `exactInt?` filtered to
  `≥ 0`, so bit/shift/mod ops (which solc errors on for negatives) and unsigned
  targets still reject negatives.
- `Expr.numberLiteralRat?` / `untypedNumberLiteralRat?` gained a real
  `unary neg` case (negate the numerator; the old untyped "only if zero" guard is
  gone). New `Expr.numberLiteralInt?` folds to a signed integer.
- `Expr.toCoreNumericLiteralAs?` **collapsed**: fold once to a signed `Int`, then
  one signed range test per target — `uint`: `0 ≤ v < 2^bits`; `int`:
  `−2^(bits−1) ≤ v ≤ 2^(bits−1) − 1`. solc rules (2) range and (3) sign fall out
  of this single test, removing the old syntactic-top-level-unary-minus branch
  (`negatedNumberLiteralNat?`, `uint/intPositive/NegativeLiteralFits` deleted).
- `TypeCheck.fixedPointLiteralRaw?` adjusted for the signed numerator (positive
  path; negatives still handled by the sibling `negatedFixedPointLiteralRaw?`).
- Everything stays **total** (no `partial`); `Option` kept only for the genuine
  partial ops (den 0, non-integer operand).

**The fix (importer):** `type_from_expression_node`'s array-length in
type-expression position (`solc_ast_to_lean_source.py`) gained the same
already-folded `typeString`/`typeIdentifier` fallback the VariableDeclaration
array-length path already had, so a scientific/unit length like `uint8[1e1]` in
that position imports instead of aborting.

**Regression guard:** new `rational-constants` corpus lane
(`tests/forge-harness/rational-constants/`, manifest case): a Forge test pins
solc's EVM values for the folded constants (incl. −5 / −7 / −93); `solc_rejects`
pins solc's rejection of `7/2 → int256` (non-integer) and `0-1 → uint256` (signed
→ unsigned); Lean witnesses (`SolidCore.Witness.RationalConstants`) pin the three
folds to their exact signed values, their acceptance into `int256`, and that the
two rejection-boundary probes still return `none` — so the Int-widening does not
over-correct into unsoundness.

`lake build SolidCore` green; the new lane is green
(`solc_rejects=ok forge=ok lean=ok`).

## 2026-07-06 — Phase 6 item 8: delete 3 orphan `*UnderResponder` wrappers

`CheckedContract.constructUnderResponder`, `constructFromUnderResponder`, and
`callCalldataUnderResponder` (`Checked.lean`) were thin wrappers over
`constructResponder`/`constructFromResponder`/`callCalldataResponder` left behind
by the Phase-5 stage-3 responder conversion. Re-verified zero references anywhere
(SolidCore/, manifest.json, scripts/ — each name appeared only on its own `def`
line) and deleted them. The used siblings
(`callTargetWithContextUnderResponder`, `callCalldataAtFromWithContextUnderResponder`,
`callFunctionWithContextUnderResponder`) are kept.

Gate: `lake build SolidCore` + smoke.

## 2026-07-06 — Phase 6 item 6: machine-checked two-external-call demo witness

Phase 5's acceptance included a *synthetic* demo tree (`phase5DemoTree`,
`Interpreter.lean` ~2204) that calls `emitLowLevelCall` twice with hardcoded
addresses — it never runs the evaluator. Item 6 hardens this: a **real**
two-external-call execution as an explicit interaction tree.

`SolidCore/Witness/Phase5Demo.lean` (new, imported by the `SolidCore.lean`
library root so `lake build SolidCore` compiles it) elaborates the existing
hand-built `lowLevelStaticDelegateFunction` (`probeBoth`: a `staticcall` then a
`delegatecall`) to a core `FunctionDef`, drives it through the real evaluator
(`FunctionDef.call`, the tree-returning entry), and:

- `phase5RealDemoTranscript` folds `SolI.queryTranscript` under the scripted
  responder answerer, exposing the raw ordered `Query` transcript over the shared
  alphabet;
- `phase5RealDemoTranscriptMatches` asserts the transcript is exactly two
  external-call queries to `0xcafe` **plus** the folded results
  (`lowLevelStaticDelegateMatches`).

**Observed / pinned:** the deterministic child-evaluation order emits the
`delegatecall` **first**, then the `staticcall`, even though the source tuple is
`(staticcall(...), delegatecall(...))`. The responder keys on
kind/target/calldata (not order), so results are unaffected; the transcript pins
the emission order, which the roadmap flags as load-bearing.

**Machine-check without axioms, without touching the frozen manifest.** Chosen
route: built-but-not-manifest. An in-kernel `decide` proof of
`phase5RealDemoTranscriptMatches = true` is infeasible (the kernel cannot reduce
the interpreter through `FunctionDecl.toCore?` + fuel-8 execution — `decide`
fails in ~1.5 s), and `native_decide` is avoided to keep the axiom set empty.
Instead a throwing `#eval` guard (`throw (IO.userError …)` on `false`) is enforced
by the compiled evaluator exactly like a harness `#eval`: `lake build SolidCore`
fails if the demo regresses (negative test confirmed — flipping the expected
kind order fails the build with the guard's message), and no proof axioms are
introduced. The frozen conformance manifest (99 cases / 426 evals) is untouched.

Gate: `lake build SolidCore` + smoke (28 cases, `forge_interpreter_compare=pass`).

## 2026-07-06 — Phase 6 item 7: harden the frozen `?` adapters (fail-open → fail-closed)

`FunctionDef.call?`, `Contract.call?`, `Contract.callTransaction?`
(`Interpreter.lean`) and `Stmt.eval?` (`Interface.lean`) folded their
interaction tree with `SolI.run context` (equivalently `contextAnswer`, i.e.
`Query.defaultAnswer`), which answers *any* stray external query fail-open with
the default (failed-call) answer and continues. Redefined all four to fold
**fail-closed** under an empty scripted responder, `SolI.runWith []`: an external
request with no matching row aborts with `ResponderFailure.unmatched` →
`.error _ → none`. `FunctionDecl.call?` inherits the fix (it delegates to
`FunctionDef.call?`).

**Why it is safe / behaviour-identical today.** These entry points reach only
query-free paths (no external call/create is emitted on them — the corpus's
oracle-bearing witnesses fold under real responders via the `*UnderResponder` /
`*FailOpen` twins, not these adapters). Verified: **zero** manifest evals
reference any of the four `?` adapters, so no eval can regress. The point is
forward-looking: a future fixture edit that routes an external call through a
non-responder entry now fails **loudly** instead of silently continuing on a
fail-open failed call.

**One proof updated (not a behaviour change).** `FunctionDef.call?_reverted_rolls_back`
(`Interpreter.lean`) `simp`ed with `SolI.run`; its revert path is a
`.done (.ok (CallResult.reverted …))` leaf, on which `SolI.runWith [] = SolI.run`
definitionally, so the theorem still holds — the `simp` lemma was switched
`SolI.run → SolI.runWith`. (This is the repo's one interpreter-side theorem; the
witness/example folds that call `SolI.run` directly are unaffected — only the `?`
adapters changed.)

Gate: `lake build SolidCore` + smoke; witness truth values unchanged.

## 2026-07-06 — Phase 6 item 9 (N2): delete the byte-memory shadow

The `Runtime` byte-memory shadow (`memoryByteMap`, `memoryBytesUsed`,
`memoryFreePointer`, `memoryAllocations` + readers `loadMemoryByte?`/
`readMemoryBytes?`, writer `noteMemoryAllocation`/`noteMemoryBytes`) was written
at `Expr.newBytes`/`newDynamicArray` and read by **nothing semantic** — only by
the witness `memoryAllocationFootprintMatches` (+ its `Expected*` helpers), which
is **not** manifest-referenced (verified 0 across manifest.json). Per the
roadmap's no-speculative-interfaces rule (the shadow misleads future
memory-refinement work), deleted together:

- The 4 `Runtime` fields, `noteMemoryAllocation`/`noteMemoryBytes`,
  `loadMemoryByte?`/`readMemoryBytes?`, and their now-dead support
  (`MemoryByteMap` abbrev + its 4 methods, `MemoryAllocation` struct,
  `initialFreeMemoryPointer`, `roundUpToWordBytes`, and the four
  `dynamic{Bytes,Array}Memory{Footprint,Content}` helpers — all shadow-only,
  verified). `bytesPrefixRightPadded` (widely used) and the **semantic**
  `Context.checkMemoryAllocation` guard (can revert on over-allocation) are kept.
- The two allocation call sites drop the `noteMemoryAllocation` write, keeping
  `checkMemoryAllocation` and threading `runtime'` unchanged (the shadow was the
  only thing the write touched — behaviour-preserving for every semantic field).
- The witness `memoryAllocationFootprintMatches` + `memoryAllocationFootprint{
  Expected,ExpectedFreePointer,ExpectedRegions,ExpectedBytes}` in
  `Witness/Interface.lean`. Kept `memoryAllocationFootprintBody`/`…Function`,
  which are shared with the (non-shadow) `checkedMemoryAllocationFootprint*`
  witnesses that just run the function and check its return value.

Gate: `lake build SolidCore` + smoke; witness truth values unchanged.

## 2026-07-06 — Phase 6 item 9 (N3): move in-file examples out of `Interpreter.lean`

De-monolith: the example/demo defs living inside the semantics file moved verbatim
(names + `SolidCore.Solidity.Source` namespace preserved) to a new
`SolidCore/Witness/InterpreterExamples.lean` (imported by the `SolidCore.lean`
root). Moved: the synthetic `phase5DemoTree`/`phase5DemoTranscriptLength` demo and
the statement/expression example corpus (`compositionalControlExample`,
signed-arithmetic, ternary/do-while, revert/require/assert, `captureReturn`,
`writesThenReverts`, …) with their little AST-builder helpers (`uint256`,
`Expr.add`, `Stmt.seq`, …). Verified zero external references to any moved def
(none manifest-referenced; the builder helpers are not called outside the block),
so the move is behaviour-neutral. `Interpreter.lean` no longer carries example
scaffolding.

Gate: `lake build SolidCore` + smoke.

## 2026-07-06 — Phase 6 status: awaiting the final sequential replay gate

All Phase 6 work items are committed (docs 1–5 at `2c3262d`, item 8 at
`50f1ca4`, items 6/7/9 at `e687bed`). Two things remain, and neither is
pre-claimed here:

1. **Item 10** — the clean sequential full replay + AST audit is RUNNING
   (nohup-detached, started 18:06 PDT) against exactly this tree. Phase 6 is
   complete only if it ends `forge_interpreter_compare=pass`, `cases=99`,
   `paired_cases_passed=yes`, with a clean audit.
2. **Item 11** — the final run-summary entry (phases, corpus status, every
   deviation, open items) is drafted and will be committed as the follow-up
   entry to this one, with the replay result and sequential wall-clock number
   (vs the ~20–25 min pre-Phase-5 baseline; >~2× triggers the recorded
   fused-run deferral) filled in from the actual run.

This entry exists so the tree can be branched from now: any worktree taken
from this commit carries the complete Phase 6 code/docs state; only the gate
verdict and the summary text land after it.

## 2026-07-06 — B/C soundness backlog: fix the three Forge-confirmed WRONG-VALUE bugs (W1/W2/W3)

Landed the three WRONG-VALUE soundness fixes from `docs/bc-soundness-audit.md`
(all Forge-confirmed against pinned solc 0.8.35). Each fix ships with a
regression lane pinned in the SAME commit; the corpus freeze exception for
pinning discovered bugs was used. Eval-count delta: **+6 Lean evals** (99 cases
unchanged; no new case created — the lanes extend the two most-fitting existing
families).

**W3 — signed-base exponentiation crash.** `applySignedWord` had no `exp` arm,
so `(-2)**2` hit the `typeMismatch` sentinel (panic 0). Added `checkedSignedExp`
/`checkedSignedExpLoop` (Interpreter.lean): two's-complement modular
exponentiation over the exponent magnitude, per-step int256-range check in
checked mode (`RevertData.overflow`), wrapping via `signedToWord` unchecked.
Added the `exp` arm to `applySignedWord` and to the `Value.int`/`Value.word`
dispatch. Narrow-type (`intN`) result overflow is enforced by the enclosing
`intCleanup` the importer already inserts — Forge-pinned boundary:
`int8(-2)**7 == -128` (fits), `int8(-2)**8` panics `0x11` (checked),
`== 0` unchecked. Lane: `checked-arithmetic` gains `negBaseEven`(=4),
`negBaseOdd`(=-8), `negExpOverflow`(panic 0x11) + 3 Lean evals.

**W2 — narrow left-shift spurious overflow panic.** Solidity shifts truncate to
the operand width with NO overflow check, even in a checked block; we wrapped the
shift result in the checked `uintCleanup`/`intCleanup`. Fix: `Ty.implicitCleanupCore?`
(Interface.lean) now detects a left-shift (`Source.Expr.binary BinaryOp.shl`) and
cleans it with the truncating `uintCast`/`intCast` (never-panic) instead of the
checked cleanup; the compound-assign path (`<<=`) applies its `ValueCleanup`
unchecked for `shl` in the `assignOpCleanupExpr` interpreter arm. Right shifts
(`shr`/`sar`, magnitude non-increasing) are untouched. Forge-pinned:
`int8(64)<<1 == -128`, `uint8(255)<<1 == 254` (no revert). Lane:
`checked-arithmetic` gains `shlWrapSigned`, `shlTruncUnsigned` + 2 Lean evals.

**W1 — `abi.encodePacked` narrow-width loss.** Top-level narrow `uintN`/`intN`
packed to a full 32-byte word instead of N/8 bytes, corrupting every
`keccak256(abi.encodePacked(...))`. Design chosen: **thread the surface top-level
byte width into the packed-encode node** rather than adding narrow constructors
to the core `Source.Ty` (which would have rippled into every exhaustive `Ty`
match — `defaultValue`, `coerceValue?`, `abiStaticBytes?`, decode, … — the
"balloon" the audit warned against). Concretely: `abiEncodePacked` now carries a
parallel `List Nat` of per-argument packed widths (`0` = "type-directed packing",
which stays correct for `bool`/`address`/`bytesN`/`bytes`/`string`/arrays/
`uint256`/`int256`); `Ty.packedTopWidth` computes N/8 for narrow `uintN`/`intN`;
`abiEncodePackedNarrowScalar?` emits the two's-complement low bytes (correct for
both `uintN` and `intN`, e.g. `int8(-1) -> 0xff`). **Array/struct elements are
deliberately left on the 32-byte-padded path** — that is exactly solc's packed
encoding of aggregates (confirmed: the pre-existing `packedUint8Array` lane
expects `encodeWord 1 ++ encodeWord 2`), so the corpus-green array/`uint256`/
`address`/`bytesN`/`bytes` behavior is undisturbed. All six call sites (two
`abi.encodePacked`, four `bytes/string.concat`) and both witness call sites
(`Witness/Checked.lean`, `Witness/Interface.lean`) updated. Forge-pinned:
`encodePacked(uint8 0x12, uint8 0x34) == hex"1234"`, `uint16+uint24 -> 5 B`,
`int8(-1) -> ff`, `uint32 -> 4 B`, `(true,false,uint8 7) -> hex"010007"`. Lane:
`abi-encoding-helpers` gains 5 narrow-scalar functions + 1 Lean eval.

**Known residual (documented, not a regression):** `abi.encodePacked(<enum>)`
still emits 32 bytes rather than 1. Enums always pack to 1 byte in solc, but the
env-less packed elaboration path (`Args.toAbiEncodeSource?` -> the
`storageNames`-only `Expr.abiTy?`) does not resolve an enum member expression to
`Ty.enum`, so `packedTopWidth` sees a width-0 type. Resolving it needs the enum
declaration env threaded into that path — beyond the surgical W1 fix and not a
regression (it was 32 bytes before). The `packedEnum` function + its Forge
assertion are kept (solc-truth = `hex"02"`); only the Lean side omits the enum
assertion. Filed as a follow-up.

**Gates.** `lake build SolidCore` green (1094 jobs). `scripts/smoke_replay.sh`
green. All three lanes green via `--only` (`checked-arithmetic`,
`abi-encoding-helpers`: `forge=ok lean=ok`, `forge_interpreter_compare=pass`).
Re-run probe outcomes now match Forge: `packedU8 -> [0x12,0x34]`,
`packedMixedWidth -> [..0x9a]`, `packedNegInt8 -> [0xff]`, `packedUint32 -> 4 B`,
`packedBoolMix -> [1,0,7]`; `negBaseEven -> 4`, `negBaseOdd -> -8`,
`negExpOverflow -> panic 0x11`; `shlWrapSigned -> -128`, `shlTruncUnsigned -> 254`.

## 2026-07-07 — Latent red lane: `openzeppelin-ecdsa` eval #4 emitted an unanswered ecrecover query under the fail-closed plain adapter

**Symptom.** `--only openzeppelin-ecdsa` errored on one eval with
`TypeError.unsupported "checked executable contract call OpenZeppelinECDSAHarness"`
— a fail-closed diagnostic escaping to the eval result (RC=1). Latent on
`codex/solidity-semantics-only` since Phase 6 `e687bed`.

**Root cause (traced, cited).** The ecdsa manifest has 5 evals. Evals #1/#2
(`tryRecoverVRS`/`recoverVRS`/`recoverShort` success paths) were already
converted to `callFunctionWithContextUnderResponder` with an `ecrecover`
oracle row. Evals #3 (high-S) and #4 (invalid-signer) still used the plain
`CheckedContract.call` with `State.empty` and NO responder. `e687bed` hardened
the plain adapter from fail-open (stray query answered with failure) to
fail-closed (`SolI.runWith []` -> `ResponderFailure.unmatched` ->
`TypeError.unsupported`, via `optionToExcept ("contract call " ++ decl.name)`,
`Checked.lean:290`). The catch: **whether a query is emitted depends on the
input**:

- Eval #3 (high-S, `s > halfOrder`): `OpenZeppelinECDSA.tryRecover`
  (`src/OpenZeppelinECDSA.sol:57-62`) returns `InvalidSignatureS` **before**
  reaching `ecrecover` at line 64. `recover` -> `_throwError` reverts, also
  before `ecrecover`. **No query is emitted** -> the plain fail-closed call
  succeeds. Eval #3 is therefore a *meaningful* fail-closed assertion that the
  high-S path never touches the precompile; left as plain `call` deliberately
  (converting it would mask a future regression where high-S wrongly reaches
  ecrecover).
- Eval #4 (invalid signer, `v = 29`, `s = 0xbbbb < halfOrder`): passes the
  S-check, reaches `ecrecover(hash, 29, r, s)` at line 64, which **emits a
  staticcall query to precompile 1** (`emitPrecompileWord`,
  `Interpreter.lean:1831`). `recoverVRS` emits a second. With no responder the
  first query is `unmatched` -> the observed error. **This is the failure.**

**Fix (manifest-only, no Lean change).** Converted eval #4 to
`CheckedContract.callResponder` (`Checked.lean:619`) — the fail-closed
responder-folding twin of the plain `call` (folds `callTree` =
`Source.Contract.call`, so the target-based semantics and the
`CallResult.reverted (RevertData.custom "ECDSAInvalidSignature" [])`
representation are byte-identical to the old plain path). Rows:
`responderOfResults [ecrecoverResult] []` with `ecrecoverResult` keyed on the
exact `(staticcall, precompile-1, ecrecoverInput hash 29 r s, value 0)` the
source emits, `success := true`, `output := []` (empty). Real EVM ecrecover on
an invalid `v` (=29) returns success with empty data;
`Precompile.outputWord?` (short output -> `none`) then yields signer =
`address(0)`, so `tryRecover` returns `(0, InvalidSignature, 0)` and `recover`
reverts `ECDSAInvalidSignature` — matching both the Forge assertions
(`test/OpenZeppelinECDSA.t.sol:70-98`: `recovered == address(0)`,
`RecoverError.InvalidSignature`, `ECDSAInvalidSignature` revert) and the
eval's pre-existing expectations. Kept as target-based `callResponder` rather
than switching to `callFunctionWithContext*` to preserve the exact revert
shape; no new Lean wrapper needed, so no build required. Eval count unchanged
(5).

**Did any expectation encode fail-open behavior contradicting Forge? No.** Under
the retired fail-open path the stray ecrecover query was answered with
failure (success=false / empty), which also decodes to `address(0)` — so
fail-open here *coincided* with Forge's real assertion rather than
contradicting it. The eval's expected values (`signer 0`, `err 1`, `arg 0`,
`ECDSAInvalidSignature`) were already Forge-truthful; only the plumbing
(unanswered query) was wrong. No expectation was weakened; the fail-closed
hardening was not touched.

**Process lesson.** The `e687bed` fail-closed hardening was gated by
`smoke_replay.sh` + witness baseline, **neither of which includes
`openzeppelin-ecdsa`**. Its true gate — the full sequential replay that
exercises every corpus case's every eval — kept getting killed, so the
regression shipped and stayed latent for the commits between `e687bed` and
`223e4d8`. Input-dependent query emission (eval #3 emits nothing, eval #4
emits) is exactly the class of bug a curated smoke cannot see. Lesson: a
fail-open -> fail-closed flip must be gated by the *full* replay, not the
smoke subset, before landing; if the full replay can't be run to completion,
the flip is unverified.

**Gates.** `lake build SolidCore` green (1094 jobs, no-op — manifest-only).
`--only openzeppelin-ecdsa`: `forge=ok lean=ok`,
`forge_interpreter_compare=pass`; all 5 evals `Except.ok true`.
`scripts/smoke_replay.sh` green.
## 2026-07-06 — Function-boundary refactor, stage 0: pin the recursion/deep-nesting gap

Branch `refactor/function-boundary` (worktree, based at Phase-6 checkpoint
`1a69f5d`), executing `docs/function-boundary-refactor-plan.md`.

Stage 0 records and pins the acceptance gap from the plan §1.4 with a paired
corpus lane, `recursion-gap` (100th case):

- Fixture `tests/forge-harness/recursion-gap/src/RecursionGap.sol` has
  (a) a genuinely recursive `factorial` (→120 at n=5), (a') `sumTo` whose
  runtime recursion depth itself exceeds the 64 inline horizon (`sumTo(70)=2485`),
  and (b) a **static, non-recursive** call chain of depth 70 (`step0..step70`,
  `deepChain()=70`). Forge test asserts all three; solc 0.8.35 accepts and
  Foundry-EVM runs them (3/3 pass).
- The recursive functions are `public` (not `external`): solc rejects internal
  self-calls by name on `external` functions ("undeclared identifier … not yet
  visible"), so recursion must be `public`/`internal`. Recorded because it is a
  non-obvious fixture constraint. `deepChain` stays `external` (it calls an
  `internal` chain, does not self-recurse).
- **Honest Lean expectation, pinned today**: the gap lives in *elaboration*, not
  typechecking — `importedContractAccepted` (the typechecker) is `true` (asserted
  as `importedContractTypechecks`). Elaboration (`toCoreContract?`) returns
  `none` because `defaultInternalCallInlineFuel = 64` runs out on the recursion /
  deep nesting, so `CheckedInput.ownCall?` returns `none` for **every** function
  of the contract. The three `*RejectedToday` witnesses assert exactly that
  (`(ownCall? … ).isNone = true`), each documented to FLIP to the concrete value
  at stage 5. Using the Option-returning `ownCall?` + `.isNone` (rather than the
  `Except`-returning `checkedOwnCallWordMatches`, whose failure is an
  `Except.error` with a fragile message) keeps the pin a clean `Bool`.
- ROADMAP gap-registry row updated (Deferred → In progress, pinned by this lane).

Gate: `lake build SolidCore` green (baseline); single-lane Lean replay
`forge_interpreter_compare=pass`, `paired_cases_passed=yes`; Forge suite 3/3.
Full replay deferred (the main tree is mid sequential replay; CPU caution).

## 2026-07-06 — Function-boundary refactor, stage 1: core node + table + evaluator arm (dead code)

Landed the target representation as dead code — nothing emits `Stmt.internalCall`
yet (elaboration still splices), so the corpus is neutral by construction.

Interpreter (`SolidCore/Solidity/Interpreter.lean`):
- New `Stmt.internalCall : List String -> String -> List Expr -> Stmt`
  (targets, resolved callee name, arg exprs).
- `InternalFunction` (name/params/returns/body) + `abbrev FunctionTable`
  + `FunctionTable.lookup?`, defined before the eval block (they cannot live in
  `Context`, which precedes `Stmt`). `FunctionDef.toInternal` projects the
  entry-only `FunctionDef` onto it; `Contract.table` maps all functions.
- The `Stmt.eval` mutual block (eval/evalList/evalWhile/evalDoWhile/evalFor)
  gained a `FunctionTable` parameter (2nd, after `fuel`), threaded through every
  recursive call.
- `internalCall` arm (§3.1): eval args in the caller runtime; look up callee;
  build the callee frame; **REPLACE** `runtime.locals` with `[frame]` (state
  shared); recurse `Stmt.eval (fuel-1) table …`; map the body `Result` exactly as
  the entry `callBodyResult` for returned/normal (restoring the caller's saved
  locals, keeping the callee's state), propagate `selfdestructed`/`reverted`, and
  map `broke`/`continued` to `reverted typeMismatch` (fixing the latent
  `captureReturn` passthrough).
- R3 mitigation: `collectReturnBindings`/`coerceReturnBindings` are the single
  source of truth; `FunctionDef.collectReturns`/`coerceReturnValues` now delegate
  to them, so the entry mapping and the internal-call arm cannot drift.
- `table` threaded through `evalBodyEntry`/`call`/`call?`/`callUnspecifiedResults`/
  `CallsUnspecified` (after `fuel`) and the rollback theorem. `Contract.call`
  passes `contract.table`.

Caller updates:
- ABI.lean (6 fallback/receive sites) pass `contract.table`; Checked.lean (9
  sites) pass `contract.core.table`; Interface.lean constructor sites pass
  `contract.table`, the two bare single-function adapters pass
  `[function.toInternal]`; `Stmt.eval?`/`Stmt.evalFailOpen?` gained a
  `table := []` default (their ~40 witness callers are unchanged).
- `FunctionDef.callFailOpen?` puts `table` LAST with default `[]` so its ~24
  external-effect witness sites in `Witness/Interface.lean` compile unchanged.
  This is correct while elaboration still splices (stages 0–1: bodies contain no
  `internalCall` nodes). At stage 2 the sites whose bodies gain internal calls
  get `contract.table`, guarded by the full replay. (The value-producing
  `call`/`call?` adapters keep `table` after `fuel` and already pass real
  tables.)

Witnesses: `SolidCore/Witness/InternalCall.lean` (imported by `SolidCore.lean`)
pins the arm with `#guard`s on hand-built tables: direct recursion
(factorial 5=120, 3=6, 1=1), frame isolation (a callee reading the caller's
`secret` reverts; the caller's locals survive), state sharing (a callee's storage
write reads back 42), `broke`→`reverted typeMismatch`, `selfdestruct`
propagation, the fuel bound (value at 64, `outOfFuel` at 3), and a missing-callee
defensive revert.

Gate: `lake build SolidCore` green (1095 jobs); `scripts/smoke_replay.sh`
behaviour-green — all 28 curated cases compute the expected values
(`Except.ok true` / `true`), including the external-effect query paths
(low-level/high-level calls, contract creation, create options) confirming
transcript invariance. Corpus neutral (no node emitted yet).

Environmental note (not a correctness issue): the smoke's `reference-assignments`
lane reported `timeout_after_600s` when run at `jobs=10` — the main tree's
long sequential replay was still competing for CPU/RAM, and ~20 concurrent
`lake env lean` processes (each ~700 MB) caused swapping that pushed this heavy
case's *wall*-clock past the 600 s per-case cap while its CPU need is ~245 s.
Re-run **solo** on the freed machine it passes cleanly:
`case_result=… lean=ok`, `forge_interpreter_compare=pass`,
`paired_cases_passed=yes`, `5:11.99` wall. The other heavy cases
(`openzeppelin-erc20`, `openzeppelin-vesting-wallet`) completed in the concurrent
run. Recorded as an R1 perf datapoint to compare at stage 2's full replay +
wall-clock (the plan's R1 measurement point); Stage 1 changes are behaviour-
neutral (elaboration still splices, no `internalCall` nodes emitted), so this is
not attributable to the node/arm as a correctness matter.

## 2026-07-06 — Function-boundary refactor, stage 2 handoff: verified edit surface (no code changes)

Stages 0–1 are committed (`e5a9876`, `58b6cf0`); stages 2–5 were deliberately
not attempted this run (each `Interface.lean` iteration is a ~7–20 min compile
and stage 2 is full-replay-gated). This entry records the VERIFIED edit surface
for stage 2, mapped against the committed tree, so the implementer starts from
checked anchors. Key facts (line numbers as of `58b6cf0`):

- `CoreStmt` IS the interpreter's `Stmt` (`Interface.lean:27` abbrev), so
  elaboration emits `Source.Stmt.internalCall` directly; the constructor exists
  (`Interpreter.lean:6155`) and the evaluator arm handles it (`:7038–7091`).
  **No other exhaustive core-`Stmt` match needs a new case** — the eval-block
  helpers delegate to `Stmt.eval`, and every `Interface.lean`/`TypeCheck.lean`
  `Stmt` traversal (renameIdents, toCore?, expandUsing, annotateAbi, …) is on
  the *surface* AST `Stmt`, a different type. No Yul/Sc lowering file exists yet.
- `FunctionDecl.internalCallParts?` (`Interface.lean:10401–10516`, two symmetric
  branches: contract functions `:10408–10460`, freeFunctions `:10461–10515`).
  At the emit point: the resolved callee decl is in scope (`callee`), and the
  ordered surface arg exprs are `sourceArgs` — but the current code produces
  arg-temp DECLS (`toStorageAwareCoreArgDeclsWithInternalAliases?`), not core
  arg exprs. Stage-2 work at this site = compute the callee table key + elaborate
  `sourceArgs` to `List CoreExpr` + return an `internalCall`-shaped result; the
  10 wrapper callers (`:10518–10869`: internalStatementCallCore?,
  internalSingleReturnCallCore?, …AssignReturn…, …Tuple…, internalReturnCallCore?)
  each own the `targets`.
- **Table key**: `FunctionDecl.coreName?` (`:8684–8689`) is what
  `FunctionDecl.toCore?` puts in `FunctionDef.name` (`:16502`), so it is the
  consistent key. Library helpers are already mangled uniquely
  (`libraryHelperName`/`…ForIndex` `:15078–15086`) and super-helpers are named by
  `FunctionDecl.superHelpers` (`:473`) BEFORE `internalCallParts?` runs. The one
  real gap: **plain contract-internal overloads share `coreName?`** — stage 2
  must add a disambiguating key (signature suffix or an overload index like the
  library scheme) used identically at the call-site emit and the table emit (R6:
  enforce by a single shared helper, not convention).
- **Table construction**: `ContractDecl.directCoreFunctions?`
  (`:18054–18080`) currently filters to
  `FunctionDecl.isCoreEntrypoint && body.isSome` (`:18078–18079`;
  `isCoreEntrypoint` `:8701–8705` returns false for internal/private). Relaxing
  this filter to also map `FunctionDecl.toCore?` over non-entrypoint direct
  functions + the helper sets already assembled in `toCoreFromOrders?`
  (`ordinaryFunctions ++ superHelpers ++ baseHelpers ++ libraryHelpers`,
  `:18457–18468`) emits the internal-linkage `FunctionDef`s; `selector? := none`
  falls out automatically (`abiSelector?` at `:16563` is none for internal), and
  `Contract.table` (`Interpreter.lean:7745`) then materializes the table with NO
  `CoreContract` shape change. Dedup caution: library/super helpers repeat across
  the dispatch order — dedup by name when emitting, or table keys collide.
- **Stage-4 deletion list** (after stages 2–3 replays are green):
  `defaultInternalCallInlineFuel` (`:10129`) + its 4 consumption sites
  (`:14680, :16551, :18155, :18200`), the fuel decrement in `internalCallParts?`
  (`:10446–10457`/`:10501–10512`), and the fuel-0 fallback
  `functionExpandModifiersToCoreWithStorageRefsOnly?` (`:9991`) whose `[]` case
  reaches `Expr.toCore?`'s `| _ => none` — the exact rejection the stage-0
  `recursion-gap` lane pins.

## 2026-07-06 — Function-boundary refactor, stage 2: node emission for value-signature contract-internal + free functions

Elaboration now emits `Stmt.internalCall` nodes (instead of splicing callee
bodies) for internal calls whose resolved callee has a **pure stack-value
signature** — every parameter and return has no data location (`location.isNone`)
— and whose name is not a synthetic `__`-prefixed helper. All other callee kinds
(storage-ref / memory-ref / function-pointer parameters or returns; library
`__library_*`, super/base helpers) keep the existing inline-splice path; they
move to the boundary in stage 3 or stay spliced where the frame model cannot
represent them yet.

**R6 table-key scheme (the handoff's open design item), decided:**
`FunctionDecl.internalTableKey? = "__internal_" ++ abiSignature?`
(e.g. `__internal_factorial(uint256)`), one shared helper used identically at
the call-site emit (`valueBoundaryCallParts?`) and the table build
(`directCoreFunctions?` / `toCoreFromOrders?`). Chosen over the library
`_overload_<index>` scheme because `abiSignature?` (the existing canonical
param-type renderer, already the selector source) is order-independent —
immune to decl-list reordering — and the `__internal_` prefix makes collision
with a plain entrypoint `FunctionDef.name` impossible. Entrypoint names stay
plain: name-based dispatch (`Contract.findFunctionByName?`, `CallTarget.name`,
used by Checked/ABI/witness paths) requires them.

Mechanics:
- `FunctionDecl.valueBoundaryCallParts?` returns the same
  `(returnBindings, returnStorageRefs, prefixCore, bodyCore)` 4-tuple shape as
  `internalCallParts?`, with `bodyCore := Stmt.internalCall returnNames key
  argVars` — so all 10 wrapper callers are byte-unchanged: `captureReturn`
  around the node is a harmless passthrough (the arm maps callee returns to
  `Result.normal` internally). Guarded `return` at the top of BOTH branches of
  `internalCallParts?` (contract functions and freeFunctions).
- Arg temps use a fresh `_ic_arg_<i>` prefix, never the parameter name: the
  evaluator binds arguments to callee params positionally (`initialFrame?`), and
  param-named temps could shadow a same-named caller local read by a later
  argument expression (a hazard the old α-renaming splice masked).
- Table build: `directCoreFunctions?` additionally elaborates every
  value-boundary ordinary function (any visibility) via the same
  `FunctionDecl.toCore?` and stores it under the mangled key with
  `selector? := none` **forced** — `abiSelector?` is visibility-blind (a
  handoff-map gap: internal functions would otherwise get spurious selectors
  into `findFunctionBySelector?` dispatch). Public functions therefore get two
  entries: plain-name selector-bearing entrypoint + mangled selector-less table
  entry. `toCoreFromOrders?` appends value-boundary FREE-function entries after
  the contract groups and dedups (`CoreFunctionDefs.dedupInternalByName`,
  first-wins = most-derived-wins across the C3 dispatch order, and
  contract-over-free on key collision, matching resolver precedence).
  Constructor path needs nothing: `constructWithBases…` already passes
  `contract.table` from `toCoreFromOrders?`.
- Modifiers untouched (substitution machinery byte-stable). The callee body in
  the table is elaborated once by `toCore?` (modifier expansion included), so a
  modifier-wrapped internal callee behaves as before.

Recursion-gap lane flip pulled forward from stage 5 (recorded deviation): the
fixture's functions are all `uint256`-typed, so at stage 2 they elaborate —
`toCoreContract?` is no longer `none` and the stage-0 `.isNone` pins would now
FAIL. The manifest lane was flipped to the concrete-value witnesses the stage-0
entry promised: `checkedOwnCallWordMatches` at fuel 4000 asserting
factorial(5)=120, sumTo(70)=2485, deepChain()=70 — verified against Forge
(solo replay: `forge=ok lean=ok`, `forge_interpreter_compare=pass`,
`paired_cases_passed=yes`). Stage 5 still owns the ROADMAP registry row update
and the final full-replay confirmation.

Gate note: per Dan's instruction this run, the smoke and full replays are
DEFERRED until all stages are implemented; stage-2 gate here = full
`lake build SolidCore` green (1095 jobs, all compile-time `#guard` witnesses
intact) + the recursion-gap solo replay above.

## 2026-07-06 — Function-boundary refactor, stage 3: library/`using`/`super`/base helpers onto the boundary (value-signature slice)

- `FunctionDecl.isValueBoundaryCallee` no longer excludes `__`-prefixed names:
  library helpers (`__library_<Lib>_<f>[_overload_<i>]`), super helpers, and
  base helpers with pure stack-value signatures now node-emit through the same
  `valueBoundaryCallParts?` guard in both `internalCallParts?` branches (their
  mangled names are already overload-unique, so `internalTableKey?` stays
  collision-free: `__internal___library_Lib_f(uint256)` etc.).
- `toCoreFromOrders?` emits selector-less table entries for value-boundary
  members of `superHelpers ++ baseHelpers ++ libraryHelpers`, elaborated once
  via `FunctionDecl.toCore?` with the full contract context (storageNames,
  stateEnv, modifiers, availableFunctions) — helper bodies are pre-contextualized
  (super-rewrites and library `using`-surface expansion already applied by
  `contextualSuperHelpers?`/`libraryHelperFunctions`), matching the splice-era
  treatment which also ran no contract-name rewrites on them. Dedup order:
  contract groups, then helpers, then free functions (first-wins).
- **Expression-position hoisting: deliberately NOT generalized (deviation from
  the plan's stage 3).** The splice-era wrapper set (`internalSingleReturnCall*`,
  `internalTwoSingleReturnCalls*`, unary/binary/abi variants) already
  sequentializes every expression-position call shape this semantics accepts;
  `valueBoundaryCallParts?` slots into exactly that sequentialization, so
  observable evaluation order is inherited from the splice era rather than
  re-implemented — R4's order-fidelity risk is structurally avoided (same
  temp-decl order, same conditional structure; only the callee body's execution
  site moved). Shapes the wrappers reject (e.g. calls in loop conditions /
  short-circuit operands that the current elaboration refuses) were rejected
  BEFORE this refactor and remain rejected: no acceptance widening beyond the
  recursion/depth fix. New-shape hoisting is future work, tracked with the
  remaining-splice items below.
- **Residual splice (kept deliberately)**: callees with storage-ref, memory-ref,
  or function-typed params/returns still inline-splice (the frame model passes
  arguments by value; storage-pointer args are lowered as `storageAlias*`
  statements, not value-producing expressions). Consequence for stage 4: the
  splice machinery and `defaultInternalCallInlineFuel` CANNOT be deleted yet —
  ref-signature recursion also remains rejected (registry row will say so).
- Gate (per this run's instruction, full replays deferred to the end):
  `lake build SolidCore` green (1095 jobs); solo lanes recursion-gap,
  modifier-order, uniswap-transfer-helper, openzeppelin-multicall all
  `forge=ok lean=ok`, `forge_interpreter_compare=pass`.

## 2026-07-06 — Function-boundary refactor, stages 4-5: deletion deferred (splice still live for ref signatures); recursion lane green; registry updated

**Stage 4 (splice deletion): deferred, deliberately.** The plan's deletion list
(`defaultInternalCallInlineFuel` + 4 consumption sites, the fuel decrement in
`internalCallParts?`, `functionExpandModifiersToCoreWithStorageRefsOnly?`)
assumed ALL internal-linkage calls moved to the boundary. Under the
value-signature slice actually implemented (stages 2-3), the splice path is the
LIVE elaboration for callees with storage-ref / memory-ref / function-typed
params or returns (the corpus exercises storage-ref library callees heavily —
OZ `using`-for fixtures), so nothing on the deletion list is dead
(9 remaining references, verified). Deleting becomes possible only after the
boundary covers ref signatures: the blocker is elaboration (storage-ref args
are lowered as `storageAlias*` statements, not value-producing core
expressions), NOT the interpreter (storage pointers already exist as runtime
`Value.storageRef`/`storagePathRef`). Recorded as the follow-up work item.

**Stage 5 (flip + registry):** the `recursion-gap` lane was flipped at stage 2
(the fixture is all-`uint256`, so it elaborates as soon as contract-internal
value calls are on the boundary) and passes against Forge with the concrete
values (factorial(5)=120, sumTo(70)=2485, deepChain()=70). ROADMAP registry row
updated: **Fixed for value-signature callees; residual gap = ref-signature
callees** (recursion through storage/memory-ref signatures is still silently
rejected via the retained inline fuel). Readiness-doc D1 note: Sc now has a
source IR for value-signature internal calls (`Stmt.internalCall` +
`Contract.table`).

Final combined gate (smoke + full replay + wall-clock vs baseline) runs at the
end of this working session per Dan's instruction; results recorded in the next
entry.

## 2026-07-07 — Function-boundary refactor: final gates, R1 wall-clock, and a pre-existing ecdsa lane failure pinned to the base commit

Final combined gate (per Dan's instruction to defer per-stage replays):

- **Full replay** (100 cases, `--jobs 10`, tip `ad2a78a` + perf/semantic fixes):
  **99/100 pass in 627s wall**, `recursion-gap` green with the concrete Forge
  values, all 35 `solc_rejects` acceptance-rejection lanes still reject, all
  previously-timing-out heavy lanes (openzeppelin-erc20 / access-control /
  erc1155-pausable-supply / erc721-royalty, reference-assignments) pass.
- **The single failure is NOT this refactor's**: `openzeppelin-ecdsa`'s
  invalid-signer eval expects `ecrecover` with v=29 to yield signer 0 without a
  scripted responder row. `ecrecover` is emitted as a precompile STATICCALL
  `Query.external`; under the Phase-6 item-7 **fail-closed** adapters
  (`e687bed`, on this branch's base) an unanswered call is `unmatched` →
  `Contract.call?` = none → `executableFailure` — the eval's expectation
  depends on the retired fail-OPEN default (miss → failed call → empty output →
  `outputWord?` none → `.getD 0` → signer 0). Verified by rebuilding the
  stage-1 baseline `58b6cf0` (node emission entirely absent): the lane fails
  IDENTICALLY there. The Phase-6 checkpoint was "awaiting sequential replay
  gate" — this is what that gate would have caught. Left unfixed here
  (out of refactor scope; likely already addressed on main): fix = either a
  scripted responder row for the precompile miss in the lane eval, or a
  deliberate deterministic-precompile answering layer in the responder.
- **R1 (performance) final numbers** (erc20 probes, per-eval interpretation):
  pre-refactor 7.3s (balanceOf-shaped) / 43.3s (construct-shaped); first cut
  36.1s / 218s (~5x — eager helper elaboration + double toCore?); after the
  single-elaboration reuse + demand-driven super/base helper entries:
  12.1s / 74.4s (**~1.7x**, within the roadmap ~2x rule). Residual overhead =
  the eager internal-linkage table entries per dispatch-order contract, kept
  eager deliberately: constructors call internal functions (`_mint`) that no
  entrypoint body demands, so demand-driving them from entrypoint seeds would
  silently break construction. The harness generator now sets
  `set_option maxHeartbeats 8000000` per generated file (the 200k default was
  an implicit ~50s-per-#eval CPU ceiling that construct-heavy lanes sat just
  under pre-refactor; the per-case wall cap remains the perf gate).
- **R2 note**: fuel is now uniform statement-recursion depth — an internal call
  costs one unit and the callee body runs at `fuel - 1`. No corpus witness
  moved (fuels are generous; the recursion-gap lane runs at 4000).
- **R3/R4 evidence**: zero value drift anywhere in the corpus — the only
  behavioural fix needed was checked-ness lexicality (callee bodies run
  `checked := true` regardless of the caller's enclosing unchecked block,
  matching the splice's `Stmt.checked` wrapper; caught by inspection, pinned by
  the OZ lanes that exercise unchecked arithmetic). Evaluation order is
  inherited from the splice-era wrapper sequentialisation (no new hoisting
  shapes were introduced), so the order witnesses pass unchanged.
## 2026-07-06 — A3: `gasleft` as `Query.resource .gas` (behaviour-preserving)

`EnvWord.gasleft` no longer reads the ambient `context.gasleft` constant directly
in the expression evaluator. It now emits `Query.resource .gas` (the shared
alphabet's reserved resource arm — `EvmCompiler.Simulation.ResourceQuery.gas`,
`Answer (.resource _) = InteractionWord`) via a new `emitGasleft : SolI Word`,
resuming on the answered word. The query appears in the transcript; the value is
unchanged **by construction** because every answerer supplies the ambient
`context.gasleft` word:

- `contextAnswer` (drives `SolI.run`) gains an explicit `resource .gas` arm →
  `wordToU256 context.gasleft` (was a context-ignoring alias of
  `Query.defaultAnswer`, which would have answered `0`); other resource arms
  (`msize`) keep `defaultAnswer`. `contextAnswer` moved above `SolI.runFromContext`.
- `SolI.runFromContext` (drives `foldExpr`, constant-expression evaluation) now
  answers via `contextAnswer context` instead of `Query.defaultAnswer` — so it,
  too, returns `context.gasleft` for `resource .gas`; external shapes are
  bit-identical (`contextAnswer` external = `defaultAnswer`).
- `SolI.runWith` (fail-closed corpus responder) gains an **explicit** `resource`
  arm (previously the catch-all): resource queries are a *different* query arm
  from external call/create requests and are answered **ambiently**, never
  matched against the responder's rows nor treated as an unmatched-external miss.
  This context-free fold carries no ambient gas word, so `gas` takes the
  canonical `0` default — behaviour-preserving because **no corpus fixture emits
  a `gasleft` query** (verified: 0 corpus `gasleft` users), so no corpus value
  changes. A context-bearing fold answers with `context.gasleft`.

`buildCallRequest.requestedGas` keeps its current fill rule (explicit `{gas:}`
else ambient `context.gasleft`). Witness: `SolidCore.Witness.GasleftResource`
drives a real `gasleft()` expression through the evaluator and machine-checks (at
`lake build SolidCore` time, throwing `#eval` guard, no axioms) that the
transcript is exactly `[resource .gas]` and the folded value equals the ambient
`context.gasleft` word.

Gate: `lake build SolidCore` + smoke. ROADMAP registry row A3 → fixed.

## 2026-07-06 — A2 design: intra-frame balance accounting (self balance becomes dynamic)

**Problem.** `msg.value` never credited the callee; `address(this).balance` /
`selfbalance` read the static `context.accountBalances` oracle and value sends
wrote nothing. Real EVM credits value before body execution and debits it on a
successful value-carrying call — Solidity-observable.

**Home for the dynamic value: `State.selfBalance : Word`.** `State` is the
dynamic execution state threaded through a call (storage, transient, events,
external interactions). Self balance is a scalar there (this contract's balance);
**other addresses stay environment facts** — `EnvLookup.accountBalance` for a key
≠ `context.self` still answers from the static `accountBalances` map (the
open-world model: the environment owns the world's balances).

**Credit point — re-base at each external entry (`FunctionDef.evalBodyEntry`).**
Before `Stmt.eval` runs the body, set
`state.selfBalance := addWord (balanceAt context.accountBalances context.self) context.value`
(the environment fact for `self`, then credit `msg.value`). This is the external
message-call / constructor entry (constructor-with-value credits identically —
`constructFrom → FunctionDef.call? → evalBodyEntry`). Internal calls are spliced
in `Stmt.eval` and never reach `evalBodyEntry`, so value is credited exactly once
per external frame. `payable` acceptance already exists
(`FunctionDef.acceptsValue`); credit happens only on the accepted path (a
rejected value send reverts with no body, hence no credit).

**Why re-base (from the oracle each entry) rather than thread a persistent
balance across top-level calls.** The corpus witnesses model "the environment
sent ETH to the contract between two calls" by hand-tuning
`accountBalances[self]` in the *later* call's context to the balance observed at
read time (e.g. weth9 `totalSupply` oracle `12`; payment-splitter `400` then
`300` after a release). Re-basing from that oracle at each external entry keeps
those reads correct, while `msg.value` crediting and value-send debiting become
observable **within** a frame. A persistently-threaded balance would instead
shadow the injected oracle (a constructor crediting `0` would pin `some 0` and
override a later `accountBalances := [(self, 400)]`), breaking splitter/escrow.
Re-basing is also simpler: `selfBalance` need not be `Option`-guarded — the entry
always initializes it before any read.

**Debit point — centralized in `Runtime.recordExternalInteraction`.** Every
value-carrying external effect (low-level `call`, `.send`/`.transfer` — which
lower to `Expr.lowLevelCall` with `kind = call` — and `contractCreate` with
value) records an `ExternalInteraction` carrying the result's `kind`/`value`/
`success`. Folding the debit into `recordExternalInteraction` (a single choke
point covering all four emit sites: two `Expr.lowLevelCall` arms, the
`Stmt.tryExternalCall` arm, and both `Expr.contractCreate` arms) keeps the diff
surgical and **off** the `Stmt.eval` call-splicing regions the sibling
function-boundary worktree is rewriting. Debit amount:
- low-level call: `if success ∧ kind ∈ {call, callcode} then value else 0`
  (staticcall/delegatecall/precompiles transfer nothing → 0);
- create: `if success then value else 0`.
Subtraction is floored at `0` (saturating) — an open-world `success = true`
implies the environment accepted the transfer, but we never fabricate a
wrapped-huge balance on an inconsistent oracle.

**Failed-send behaviour.** The environment answers `success = false` → debit `0`
(EVM refunds value to the caller on callee failure). `.transfer`'s revert-on-
failure rolls back the frame anyway; `.send`/`call` observe the un-debited
balance.

**Reads.** `EnvLookup.accountBalance` at its evaluation site reads
`runtime.state.selfBalance` when the key equals `context.self`, else the static
oracle. `address(this).balance` and `selfbalance` both lower to this node with
key `= context.self`.

**Existing balance-touching corpus (audited, all stay green).** With value-`0`
entries the credit is `+0`, so the read equals the oracle base — unchanged:
- `dapphub-weth9` `totalSupply` (oracle `12`, value `0` → `12`); the deposit/
  receive credits are asserted via `balanceOf` storage, not `address(this).balance`.
- `openzeppelin-vesting-wallet`/`payment-splitter`/`refund-escrow`: entries carry
  value `0`; each reads `address(this).balance` (= oracle) *before* sending, and
  the send's debit lands after the read (or in a separate call whose asserted
  getter reads storage). The multi-stage splitter/escrow oracles (`400`/`300`,
  `125`/`44`) are re-based fresh per entry, so the hand-tuned post-release balance
  is honoured.
- Lean witness `checkedAddressMembersMatch` (`accountInfo`): self `.balance` =
  oracle `1000` at value `0` → unchanged; other-address `.balance` = static `77`.

**The one hand-tuned oracle that must change: `base-constructor-runtime-args`
`BalanceArg`.** It is the sole corpus case that both *receives* value (`10`) and
reads `address(this).balance` in the *same* entry (a constructor storing the
balance to slot 0, asserted `== 10`). Its oracle was hand-tuned to the
**post-credit** balance `accountBalances := [(0xcafe, 10)]`; under A2 that
double-counts (`base 10 + value 10 = 20`). Corrected to the **pre-credit
environment fact** `accountBalances := []` (fresh account, balance `0`), so A2's
credit reconstructs `0 + 10 = 10` — matching Forge ground truth (a fresh deploy
funded with `10` wei reports `address(this).balance == 10` in its constructor).
This is exactly the roadmap's flagged case: the lane previously passed *because*
the balance read returned a hand-tuned oracle constant; A2 makes the credit
explicit and moves the tuning to the pre-call fact.

**Pinning (paired Forge lanes).** A dedicated `balance-accounting` fixture covers
the four required scenarios against Forge ground truth: (1) a payable entry
crediting `msg.value` and reading `address(this).balance`; (2) a `transfer`/`send`
debit observable via a subsequent balance read; (3) a failed send (recipient
reverts) leaving the balance un-debited; (4) constructor-with-value crediting.
Fix + lane land together green (`--only`, the W1–W3 pattern).

Gate: `lake build SolidCore` + smoke (weth9 / vesting / splitter / escrow are the
canaries) + the new lane via `--only`. ROADMAP registry row A2 → fixed.

## 2026-07-06 — A2 consistency with the Yul (`../evm-compiler`) balance model

Checked A2's balance model against how the shared Yul/EVM semantics handle
balance (verified by reading `../evm-compiler`, read-only):

- Yul balance is a per-account `UInt256` in the threaded `OpenWorld.accounts`
  map. `SELFBALANCE` reads `codeOwner`'s account; `BALANCE` reads any account by
  address; `CALLVALUE` reads `executionEnv.weiValue`. An outgoing `CALL` with
  value is **debited from the caller and credited to the callee before the
  callee body runs** (reference EVM `Θ`, `thetaCallTransfer` producing `σ₁`
  before `Ξ`), and on failure the whole account map is rolled back — **no net
  transfer**. Across the boundary balance travels only inside the `OpenWorld`
  snapshot (`Query.external` in) and `CallResponse.postWorld` (out).

- A2 lines up **within a single external frame** (the observable it targets):
  `State.selfBalance` is the self/`codeOwner` account entry, read by
  `address(this).balance` *and* written by the outgoing-call debit through the
  same field (matching that `SELFBALANCE`/`BALANCE(self)` and the call debit hit
  one live entry); `msg.value` is credited at `evalBodyEntry` before `Stmt.eval`
  (credit-before-body); the debit fires only on `success` and nothing on failure
  — observationally equal at the caller boundary to Yul's debit-before-body +
  refund-on-failure, since the callee body is environment-answered and never
  observes our self balance mid-call. Other-address `.balance` stays the static
  oracle (= a read of `accounts.find? addr |>.balance`).

- Two **pre-existing checkpoint-1 simplifications** remain (not A2 regressions):
  (1) responders ignore `postWorld`, so self balance moves only via its own
  credits/debits, not via callee-returned world deltas; (2) balance is not a
  threaded `OpenWorld` — cross-call balance is supplied by the static oracle at
  each entry (the environment owning cross-call world state, per the open-world
  model) rather than carried in `postWorld`. The convergence (the Phase 5
  "OpenWorld-shaped environment carried in the source state" future work) folds
  `selfBalance` into a threaded `OpenWorld` and honours `postWorld`, at which
  point Solidity `BALANCE(self)`/`SELFBALANCE` and the outgoing-call debit become
  the same account-map operations Yul performs. A2 is the intra-frame stepping
  stone and does not contradict that direction.
