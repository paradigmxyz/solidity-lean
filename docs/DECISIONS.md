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
