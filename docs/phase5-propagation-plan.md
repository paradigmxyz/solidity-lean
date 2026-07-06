# Phase 5 completion plan — propagate the interaction tree to the top

Status: design, 2026-07-06. Written against `codex/solidity-semantics-only`
@ `a6d3f7d` (foundation `480d7ce` + sub-step-1a `3be51fb` committed). All
file:line references are to that tree. Every stage below ends
`lake build SolidCore` green **and** `scripts/smoke_replay.sh` green; the
full replay is the end-of-phase gate (plus one mid-phase full replay after
stage 1c, see below).

## 0. Finding: `lake build SolidCore` is RED at HEAD — stage 0 is a repair

Verified during planning: a clean checkout of `a6d3f7d` fails
`lake build SolidCore` with two errors in `SolidCore/Witness/Interface.lean`
(20834, 20893). Both are `match … with | Except.ok …` over the *raw*
expression-evaluator results (`Expr.evalBinaryWithRuntimeOrder`,
`Expr.evalWithRuntimeOrder`), which sub-step-1a changed to return
`SolI (Value × Runtime)`. The replay harness generates per-case witness
files and never builds `SolidCore.Witness.Interface`, so the sub-step-1a
"green" replay did not catch it.

**Stage 0 (validated — see §5):** wrap both scrutinees in
`SolI.foldExpr (Expr.orderFuel core + 1) unspecifiedBinaryOrderContext (…)`,
exactly as the `…ByContext` adapters do (`Interpreter.lean:5920`). The two
match arms stay byte-identical. Additionally: add `lake build SolidCore` as
a first step of `scripts/smoke_replay.sh` so a library/witness break can
never again hide behind a green replay. Commit stage 0 on its own.

## 1. Chosen control-flow model: **(A), refined** — reverts stay `Result.reverted` values; `outOfFuel` is the only throw that escapes `Stmt.eval`

### Why A and not B

1. **Try-catch never catches a nested execution's throw.** In this
   open-world semantics the try target is *environment-answered*:
   `Stmt.tryExternalCall` (Interpreter.lean 6963–7110) branches on
   `callResult.success` from the oracle answer, and catch-clause dispatch
   is `TryCatchClause.findMatch? output` on the answer's bytes (7085–7099);
   same for `Stmt.tryContractCreate` (7111–7183). Monadic `tryCatch` would
   model *nothing* that the semantics does at try/catch — model B's main
   selling point is vacuous here. (Solidus needs throw-based reverts
   because its callee *executes*; ours never does, by design — "Closed-world
   multi-contract execution: out of scope by design", ROADMAP.md.)
2. **`Result` is a six-way control-flow word, not an error channel.**
   `broke`/`continued`/`returned`/`selfdestructed` (Interpreter.lean 6117)
   must remain values regardless (they are not failures — `Stmt.evalWhile`
   consumes `broke`/`continued` as loop control, `FunctionDef.callBodyResult`
   7464 consumes all six). Making only `reverted` a throw creates two
   control-flow regimes inside one match block and forces a semantic
   rewrite of ~197 `Except` arms plus every `Result.reverted` producer and
   consumer. Model A rewrites *scrutinees only*; arms stay byte-identical.
3. **`outOfFuel` gets exactly the distinguished-truncation role the phase
   wants.** With expression reverts caught at each statement site (below),
   the only `SolidityFailure` that can escape `Stmt.eval` upward is
   `.outOfFuel` (replacing today's `fuel = 0 → none`). The top-level
   `Option` adapter is then trivially correct: `error → none` is exactly
   the old `none`, and no revert can be hiding in the `error` case.
4. **Regression risk / diff size.** A converts ~55 statement-level
   expression-fold sites + 9 lvalue-helper sites by changing the scrutinee
   expression only, plus mechanical `some/none → pure/bind` plumbing. B
   additionally changes the *meaning* of every arm that pattern-matches
   `Result.reverted` (28 producers in the block) and of
   `callBodyResult`. A is checkable with `git diff --word-diff`; B is not.
5. The eventual ForwardRel/done-relation relates *final observables*
   (CallResult-level), not the interpreter's internal control-flow
   encoding, so B buys nothing for composition either.

### The one refinement over plain A: a fuel-free top-level fold

`Interaction` is a plain inductive (`evm-interaction
EvmCompiler/Simulation/Interaction.lean:723`) whose `request` constructor
carries `Answer query → Interaction …`; `k answer` is a structural subterm.
So the top-level fold needs **no fuel**:

```lean
def SolI.run {α : Type} (context : Context) :
    SolI α → Except SolidityFailure α
  | .done r => r
  | .request q k => SolI.run context (k (contextAnswer context q))
```

**Validated to compile (PoC, §5).** This dissolves the hardest open
question of the naive plan: unlike the Expr layer (query count ≤ syntactic
`lowLevelCall` count ≤ `orderFuel`, the committed `foldExpr` invariant), a
*statement* execution's query count is NOT syntactically bounded — loops
emit one query per iteration — so no honest fuel bound exists at the
`Contract.call` boundary short of re-deriving one from `Stmt.eval`'s own
fuel. With structural recursion, none is needed. The fuel-bounded
`SolI.runFromContext` (1970) stays for the transcript utilities; nothing
above the Expr layer should use it.

### The `caught` helper — where `tryCatch` threading is load-bearing

Statement sites consume the (throw-revert) Expr trees through one helper:

```lean
def SolI.caught {α : Type} (tree : SolI α) : SolI (Except RevertData α) :=
  tryCatch (Except.ok <$> tree) (fun failure =>
    match failure with
    | SolidityFailure.revert e => pure (Except.error e)
    | SolidityFailure.outOfFuel => throw SolidityFailure.outOfFuel)
```

**Validated to compile (PoC, §5).** Correctness rests on two verified laws
of the shared monad (`Interaction.lean` 760/775): `bind` and `tryCatch`
both *thread* `request` nodes (`tryCatch (.request q resume) h = .request q
(fun a => tryCatch (resume a) h)`), so an in-flight external-call query
inside an expression survives the catch and propagates upward; only the
`done (.error …)` leaf is intercepted. This is the single point in the
whole design where those laws are load-bearing — keep `caught` the *only*
`tryCatch` use in the interpreter (greppable invariant) and say so in its
docstring. Note `caught` also converts the Expr layer's `fuel = 0` throw
(`.revert typeMismatch`, unchanged since sub-step-1a) into a value — the
same collapse `foldExpr` does today, so behavior is preserved.

### Exact types for the chain

| Function (anchor) | Today | After stage 1/1e |
| --- | --- | --- |
| `Stmt.eval` (6382) | `Nat → Context → Runtime → Stmt → Option Result` | `Nat → Context → Runtime → Stmt → SolI Result` |
| `Stmt.evalList` (7238), `evalWhile` (7248), `evalDoWhile` (7273), `evalFor` (7307) | `… → Option Result` | `… → SolI Result` |
| `LValue.resolveWithRuntime` (6029) | `… → Except RevertData (ResolvedLValue × Runtime)` | `… → SolI (ResolvedLValue × Runtime)` |
| `LValues.writeTupleWithRuntime?` (6033) | `… → Except RevertData Runtime` | `LValues.writeTupleWithRuntime : … → SolI Runtime` |
| `FunctionDef.evalBodyEntry?` (7492) | `… → Option Result` | `FunctionDef.evalBodyEntry : … → Option (SolI Result)` — `none` still means acceptsValue/frame-construction failure, a *static* absence, not an effect |
| `FunctionDef.call?` (7505) | `… → Option CallResult` | new `FunctionDef.call : … → Option (SolI CallResult)`; `call?` keeps its exact signature as adapter: `(FunctionDef.call …).bind (fun t => (SolI.run context t).toOption)` |
| `FunctionDef.callUnspecifiedResults` (7538) | unchanged (defined via `call?`) | unchanged |
| `Contract.call?` (7632), `callTransaction?` (7640) | `… → Option CallResult` | new `Contract.call` / `Contract.callTransaction : … → Option (SolI CallResult)`; `?` versions keep signatures as adapters |
| `ContractCallKind.result?` (7657) | unchanged (via `?`s) | unchanged |
| ABI `Contract.callCalldataAtFromWithContext?` (ABI.lean 669) and the `callCalldata*` family (721–800) | `… → Option CoreAbiCallResult` | new `…WithContext : … → Option (SolI CoreAbiCallResult)` (tree mapped through decode/encode); `?` versions keep signatures as adapters |
| Checked entry points (`CheckedContract.callFunctionWithContext?` Checked.lean 299, `callTargetWithContext?` 316, `CheckedProgram.constructContract*` 470–508, …) | `Option`/`Except TypeError` wrappers over `FunctionDef.call?` | **unchanged through stages 1–2** (they call the frozen `?` adapters); tree-returning twins added in stage 1e, consumed by the manifest only at stage 3 |

Design rule made explicit: **`Option` nesting outside the tree encodes
static absence** (function not found, arity/frame mismatch, ABI decode of
the *entry* calldata); the tree encodes execution. Do NOT map those
`none`s to `throw .outOfFuel` — they are not truncation. Verified: within
the Stmt mutual block (6382–7340) every `none` *source* is a `fuel = 0` arm
(6384 plus the three loop companions) and every other `none` is
propagation, so `none → outOfFuel` is exactly right *inside* the block and
exactly wrong above it (`evalBodyEntry?` 7500, `Contract.call?` resolution
7636, ABI decode failures).

The `?`-adapter for the top is one small total function next to `SolI.run`:

```lean
def SolI.run? {α : Type} (fuel : Nat) (context : Context) -- fuel unused; kept out
```
— concretely: `FunctionDef.call? … := (FunctionDef.call …).bind fun t =>
match SolI.run context t with | .ok r => some r | .error _ => none`.
(`.error` here can only be `.outOfFuel` by construction — reverts were
caught into `Result.reverted` values below — but match both, totally.)

### What happens to the `…ByContext` family

- The five folding adapters (`Expr.evalWithRuntimeByContext` 5920,
  `evalListWithRuntimeByContext` 5926, `memoryRefOrValueWithRuntimeByContext`
  5964, `resolveLValueWithRuntimeByContext` 5971,
  `evalReturnListWithRuntimeByContext` 6022) **stay defined** but leave the
  execution path. Their remaining legitimate users are pure-constant
  evaluation: `Expr.evalLayoutBaseCore?` (Interface.lean 17653) and
  `CoreExpr.evalWord?` (Interface.lean 19290), plus the stage-0 witness
  sites. Those inputs are typechecker-vetted constant expressions with no
  external-call nodes, so folding is semantically safe there; add that as a
  comment on `foldExpr` (5913), which already carries the
  `transcript length ≤ orderFuel` invariant note.
- Inside the Stmt block, every `…ByContext` call site becomes
  `← (Expr.…WithRuntimeOrder context.effectiveChildEvalOrder context r e).caught`
  — the *unfolded* tree, caught, arms unchanged.

## 2. Staged plan

Each stage = one commit, ending `lake build SolidCore` + smoke green.
Mechanical (M) = pattern-rewrite an editor/reviewer can verify arm-by-arm;
Manual (m) = requires local reasoning.

### Stage 0 — repair the red build (M, validated)
As §0. Two scrutinee wraps in `Witness/Interface.lean` 20827/20884 +
`lake build SolidCore` prepended to `scripts/smoke_replay.sh`.

### Stage 1 — thread `SolI` through Stmt + call chain; single top adapter
The big one (~1,100 lines touched, all in `Interpreter.lean`). Fixtures,
Context, ABI.lean, Checked.lean, manifest: untouched.

1. Add `SolI.run` and `SolI.caught` after `contextAnswer` (1988) —
   exact code validated in the PoC (§5).
2. Convert `LValue.resolveWithRuntime` (6029) and
   `LValues.writeTupleWithRuntime?` (6033, rename → `writeTupleWithRuntime`)
   to `SolI`. Their internal pure helpers (`resolved.write`, coercions)
   auto-lift via the committed `MonadLift (Except RevertData) SolI` (1877).
   (M; these sit *before* the Stmt block in the file, no forward-ref issue.)
3. Convert the mutual block `Stmt.eval`/`evalList`/`evalWhile`/`evalDoWhile`
   /`evalFor` (6382–7340) to `SolI Result`:
   - the four `fuel = 0 → none` arms (6384, 7240-ish, 7250-ish, 7275-ish,
     7309-ish) → `throw SolidityFailure.outOfFuel` — this is the roadmap's
     "distinguished failure constructor replaces that `none`, not just the
     outer wrappers" (m — the only *semantic* change in the stage, and it
     is invisible through the top adapter);
   - every `match <recursive Stmt call> with | some r => X | none => none`
     → `do let r ← <call>; X` (M, ~258 `some/none` occurrences; `none`
     never occurs non-propagatively inside the block — verified);
   - every `match e.…ByContext context r with | Except.ok … | Except.error …`
     (~55 sites, list from `grep -n ByContext` restricted to 6382–7340) →
     `match ← (…Order-tree).caught with` — same arms (M);
   - the 9 `resolveWithRuntime`/`writeTupleWithRuntime` sites (6525, 6535,
     6562, 6578, 6591, 6616, 6629, 6651, 6658): scrutinee → `← (…).caught`
     (M);
   - `Stmt.tryExternalCall` (6963) and `tryContractCreate` (7111): only the
     Option/Except plumbing changes at this stage; the oracle reads at 7045
     (`context.resolveLowLevelCall`) and 7132 (`resolveContractCreation`)
     stay synchronous (m — these two arms are the densest code in the file;
     convert them last, with the inner `valueGasResult?`/`saltResult?`
     Except-accumulators left as pure `Except` values exactly as they are).
4. `FunctionDef.evalBodyEntry` : `Option (SolI Result)`;
   `FunctionDef.call` : `Option (SolI CallResult)` :=
   `(evalBodyEntry …).map (·.map (function.callBodyResult state))`
   (`callBodyResult` 7464 is pure — unchanged); `FunctionDef.call?` becomes
   the adapter (PoC shape). Fix `FunctionDef.call?_reverted_rolls_back`
   (7553) by extending its simp set — exact fix validated in the PoC:
   `simp [FunctionDef.call?, FunctionDef.call, FunctionDef.evalBodyEntry?,
   FunctionDef.callBodyResult, SolI.run, Pure.pure,
   EvmCompiler.Simulation.Interaction.pure, hAccepts, hFrame, hEval]`
   (plus now `SolI.caught`-free since the tree from a `some (Result.reverted …)`
   hypothesis is `pure`; if the statement needs restating against the tree
   version, restate it — it is the roadmap's "first lemma" candidate, not a
   corpus gate).
5. `Contract.call` / `Contract.callTransaction` : `Option (SolI CallResult)`
   (7632/7640; `callTransaction` maps `CallResult.clearTransient` over the
   tree with `Functor.map`); `?` versions become adapters. (M)
6. **Why this stage is behavior-preserving:** `contextAnswer` is a pure
   function of `Context` alone (1988) — answering a query at the per-
   expression fold (today) or at the per-call fold (after) yields the same
   answer, and reverts/results flow identically. The only delta is
   `fuel = 0` propagation, identical through the adapters (`none` either
   way).
7. Gate: build + smoke. Also time the smoke run vs a pre-stage-1 baseline
   (see risk R4).

### Stage 1b — `Stmt.eval`'s low-level-call site emits (m, small)
At 7045: replace `context.resolveLowLevelCall kind target calldata value gas?`
with `← emitLowLevelCall context kind target calldata value gas?` (1932).
Keep the `missingCode` short-circuit *before* the emit — the
extcodesize-style guard (`checkTargetCode && !(context.accountHasCode
target)` → `LowLevelCallResult.failedRequest`, 7038–7043) is a state read
that produces **no query**, matching both EVM behavior and the alphabet
(environment reads stay state reads). `recordExternalInteraction` keeps
consuming the decoded result. After this stage the transcript for
high-level external calls is real. Gate: build + smoke (the smoke set
covers this surface per the smoke-replay DECISIONS entry).

### Stage 1c — creates emit, with name-encoded initCode (m + new code)
Implements the endorsed creation decision (creation is by *name*,
pre-compilation; fixtures key the oracle by name and do NOT populate
`contractCreationCodes`, so the initCode identity is a canonical name
encoding, not creation bytecode).

1. **Encoding** (new, next to `buildCallRequest` 1907):
   `creationInitCode (name : String) (args : List Byte) : ByteArray :=`
   32-byte big-endian length of the UTF-8 name ‖ name bytes ‖ args.
   Decoder `decodeCreationInitCode? : ByteArray → Option (String × List Byte)`
   parses the prefix fail-closed (length > remaining, or non-UTF-8 → `none`).
   Injective by construction; document as the source-canonical initCode —
   the residual "create initCode is not compiled bytecode" transcript
   mismatch is a recorded, gas-like deferred limitation (add to the
   deferred-gap registry in `ROADMAP.md` and `docs/DECISIONS.md`).
2. **Emit side**: `buildCreateRequest` — `kind := if salt?.isSome then
   .create2 else .create`, `creator := wordToAddress context.self`,
   `value := wordToU256 value`, `initCode := creationInitCode name args`,
   `salt := salt?.map wordToU256`, `permission := true`.
   `emitContractCreation : Context → String → List Byte → Word →
   Option Word → SolI ContractCreationResult` emitting
   `Query.external default (.create request)`.
   `decodeCreateResponse` : `CreateResponse` has **no `success` field**
   (Interaction.lean 676) — failure is `address = 0` (EVM convention):
   `success := response.address ≠ 0`, `address := u256ToWord response.address`,
   `output := byteArrayToBytes response.returnData`; name/args/value/salt
   carried through for oracle keying and `recordExternalInteraction`,
   exactly as `decodeCallResponse` (1925) does.
3. **Answer side**: `answerCreate context request : CreateResponse` —
   decode the name (malformed → the old fail-open `failedRequest` shape,
   until stage 2 makes it fail-closed), then
   `context.lookupContractCreation? name args value salt?` (1719), else
   `ContractCreationResult.failedRequest` (1472); encode back with
   `address := if result.success then result.address else 0`,
   `returnData := result.output`, `postWorld := default`,
   `returnedGas := request.requestedGas`-analog (0 — creates carry no gas
   field in the fixture oracle). **Add the `.external _ (.create …)` arm**
   to `contextAnswer` (1988) and `SolI.runFromContext` (1970);
   `SolI.run`/`queryTranscript` get it for free.
4. **Convert the 3 sites**: `Expr.evalWithRuntimeOrderFuel` creates at
   5497 and 5516 (`context.lookupContractCreation?` matches → `←
   emitContractCreation …`, keeping the success branch → `Value.word
   result.address` + interaction record, failure branch → `throw (.revert
   (RevertData.fromRawBytes result.output))` / `.revert .empty` exactly as
   now); `Stmt.tryContractCreate` at 7132 (`resolveContractCreation` →
   emit; success/catch branching on the decoded result unchanged).
5. **Consistency audit hook**: a fixture row with `success = true ∧
   address = 0` (or `false ∧ address ≠ 0`) cannot round-trip through
   `CreateResponse`; grep the fixture oracle data now and add a fail-closed
   check to the stage-2 responder derivation. Expected: none exist (EVM
   cannot produce them).
6. Note: `Expr.orderFuel`-based `foldExpr` fuel is no longer relevant to
   creates on the execution path (whole-call fold is fuel-free), but the
   committed `foldExpr` invariant comment should be updated: query count ≤
   syntactic (`lowLevelCall` **+ create**) node count ≤ `orderFuel` — the
   same argument covers the two new Expr-level query sites.
7. Gate: build + smoke + **one full replay** (create fixtures beyond the
   smoke set exist; this is the cheapest point to catch a create-oracle
   mismatch, well before the stage-2 responder conversion).

### Stage 1d — precompile builtins emit (m, small) — REQUIRED before stage 3

**Framing (corrected):** precompiles are NOT a residue family — they are ordinary
external calls. Source builtins `ecrecover`/`sha256`/`ripemd160` are, in the EVM, a
`STATICCALL` to address 1/2/3, so they emit `Query.external` like any call; the
deterministic result is computed **in the responder** (`answerCall` →
`lookupLowLevelCall?` → `builtinStaticcallResult?`/`ecrecoverAt`), not inline in
the evaluator. This is required for the eventual ForwardRel composition: the Yul
side emits these precompile staticcalls, so a source transcript that omitted them
could not compose. (`keccak256` is the KECCAK256 opcode, computed in-EVM, so it
correctly stays local — no query.)

Found during planning; not in the roadmap's three-residue list:
`Context.ecrecoverAt` (1565) and `ExternalHashKind.lookup?` (1570) read
`context.lowLevelCallResults` via `Precompile.lookup?` (1552–1557). The
roadmap's alphabet decision says precompile calls are environment-answered
external requests (Solidus-matching), and these reads *block deleting the
field* at stage 3 regardless. Convert their evaluator call sites (the
`Expr.externalHash` arm, 4365's evaluator case, and the ecrecover builtin —
locate via `grep -n "ecrecoverAt\|ExternalHashKind.lookup?"`) to emit
`Query.external default (.call request)` with `recipient/codeAddress :=`
the precompile address (1 = ecrecover, 2 = sha256, 3 = ripemd160),
`calldata := input`, `value := 0`, `kind := .call`; decode the output word
from `returnData` exactly as `Precompile.outputWord?` does. `answerCall`
already answers these (it keys the same oracle rows via
`lookupLowLevelCall?` — verify the row shape matches `Precompile.lookup?`'s
keying; if precompile fixture rows are keyed differently, extend
`answerCall` with the `Precompile.lookup?` fallback rather than changing
row data). Gate: build + smoke.

### Stage 1e — ABI + checked entries become tree-returning (M)
- ABI.lean: the three `FunctionDef.call?` uses (598, 635 constructor path,
  684) switch to `FunctionDef.call`; `Contract.callCalldataAtFromWithContext`
  (669) gains a tree-returning form `Option (SolI CoreAbiCallResult)` with
  decode (static, stays outside the tree) and result-encode (`Functor.map`
  over the tree); the ~15 `callCalldata*` wrappers (721–800) get tree twins;
  `?` versions keep signatures as adapters.
- Checked.lean: tree twins for `callFunctionWithContext?` (299),
  `callTargetWithContext?` (316), `constructWithContext?`-family, and the
  `CheckedProgram` wrappers (470–508); the existing `?`/`Except TypeError`
  entry points delegate unchanged. Interface.lean's
  `SourceUnit.constructContract*` (19145–19169) likewise.
- After this stage the roadmap's acceptance shape holds structurally:
  `Contract.call`/ABI entries ARE interaction trees; the `?` adapters are
  the single fold boundary. Gate: build + smoke.

### Stage 2 — scripted responders (m + harness/Python work)
Per ROADMAP "Phase 5 specifics" (all already decided there; listed for
completeness with this plan's additions):
1. Responder type `ScriptedResponder := List (RequestMatcher × Answer-payload)`
   applied in order, fail-closed: unmatched/out-of-order → test failure
   with an expected-vs-actual request diff. Matchers ignore the
   `OpenWorld` snapshot (checkpoint-1 rule; snapshot population is separate
   work — keep `default` worlds and `postWorld := sent world` per the
   roadmap's mechanical-conversion default).
2. Derive responders mechanically from `lowLevelCallResults`/
   `contractCreationResults` in the witness generator
   (`scripts/solc_ast_to_lean_source.py` / harness). Every request the
   replay actually sees gets an explicit entry — including
   intentional-failure entries derived from today's fail-open fallback;
   enumerate fixtures that relied on the fallback in `docs/DECISIONS.md`.
   Add the create `success/address` consistency check (stage 1c §5) and the
   name-decode fail-closed switch here.
3. **Same commit** (roadmap requirement): kind-dependent
   `buildCallRequest` fields — delegatecall: `recipient := self`,
   `transferValue := 0`, `apparentValue := context.value`; staticcall:
   `transferValue := 0`. Today's uniform mapping (1907–1920) round-trips
   only because `answerCall` inverts `recipient` alone.
4. Validation lane before flipping anything: fold every witness tree under
   both answerers (`contextAnswer` vs derived responder) and assert equal
   results and transcripts. Then flip the harness to responders.
5. Gate: build + smoke + full replay. Expectations must not change; a
   fixture whose oracle can't be expressed as a consistent responder is a
   fixture bug → roadmap's logging policy.

### Stage 3 — delete the oracle fields + one-commit manifest rewrite (M)
Blocked on 1b, 1c, 1d (all `lowLevelCallResults`/`contractCreationResults`
readers gone: `lookupLowLevelCall?` 1687, `resolveLowLevelCall` 1709,
`lookupContractCreation?` 1719, `resolveContractCreation` 1725,
`lookupPrecompileCall?` 1552, and `answerCall`'s oracle path 1946 — the
context answerer itself is superseded by responders).
1. Delete `Context.lowLevelCallResults`/`contractCreationResults`
   (1504–1505), their initializers (1531–1532, `Contract.context`
   7591–7592), and the reader functions; `SolidityFailure`-side
   emit/decode/transcript machinery stays.
2. Mechanical manifest rewrite in the same commit: ~119 witness defs / 419
   evals (manifest.json string counts: 136 `callFunctionWithContext`, 31
   `constructContract`, 38 `callCalldata`) switch from the `?` adapters to
   the tree entries folded under the fixture's scripted responder; eval
   count unchanged. The `?` adapters themselves either die here or remain
   as responder-parameterized conveniences — prefer deletion; keep names by
   redefining `?` over the responder fold so the manifest diff is
   argument-shape-only.
3. Gate: build + smoke + full replay + wall-clock comparison against the
   pre-stage-1 baseline (roadmap's ~2× rule → fused run, see R4).

## 3. Risk register

- **R1 — Conflating static `none` with truncation.** The block-internal
  audit (grep over 6382–7340) shows every `none` source is a fuel-0 arm;
  but `evalBodyEntry?` (7500: `initialFrame? = none`), `Contract.call?`
  resolution (7636), and ABI decode failures are *static* absences.
  Mitigation: the Option-outside/tree-inside rule of §1; code-review each
  `none` deleted in stage 1 against the audit list; the adapters make any
  mistake invisible to the corpus, so also add one targeted witness: a
  selector call with wrong arity must stay `none`-shaped, and a fuel-0
  `Stmt.eval` must fold to `error .outOfFuel` (new tiny `#eval`s in the
  e2e-proofs lane, not the frozen corpus).
- **R2 — `caught` swallowing or double-wrapping.** If a site uses raw
  `tryCatch` (or forgets `.caught` and `←`-binds a throwing Expr tree), a
  revert that today becomes `Result.reverted` would escape as a monadic
  throw and surface as `none` at the adapter (observable: corpus red).
  Mitigation: `caught` is the only `tryCatch` in the file (grep gate);
  every Expr-tree bind inside the Stmt block goes through it; smoke covers
  revert-heavy lanes (assert/require/revert-string sentinels are in the
  smoke set).
- **R3 — Transcription errors across the ~960-line block** (the
  `selfdestructed`/`broke`/`continued` arms especially — they are
  low-traffic and a dropped arm may still typecheck if a wildcard exists).
  Mitigation: scrutinee-only edit discipline; `git diff --word-diff`
  review pass; the loop-control lanes (`compositionalControlResult`,
  do-while/for witnesses, 7733–7860) are exactly the sentinels for
  broke/continued and are in the smoke set.
- **R4 — Performance.** Two opposing effects: stage 1 *removes* ~1 fold
  per expression evaluation but *builds* one whole-call tree (bind
  allocation across ~everything; the heavy OZ lanes run minutes today).
  Mitigation: measure, don't guess — record smoke wall-clock before stage 1,
  after stage 1, and full-replay time at stage 3 vs the pre-phase baseline;
  if > ~2×, implement the roadmap's fused run: `SolI.runDirect` = answer at
  emit time (an answerer-indexed evaluator), checked against tree-then-fold
  on the corpus. The fuel-free `SolI.run` also avoids the quadratic
  re-descent a fuel-retry loop could cause. Lean-specific note: the
  `Interaction` bind is not tail-recursive over `request` chains; deep
  loops with many queries could deepen the fold stack — bounded by query
  count, which today's fixtures keep small (verify max transcript length
  during stage 2 derivation and record it).
- **R5 — Theorem/manifest coupling.** `call?_reverted_rolls_back` fix is
  validated (PoC). Manifest churn is confined to stage 3 by the frozen `?`
  signatures — enforce with a stage-1..2 invariant: `git diff` must not
  touch `tests/forge-harness/manifest.json`.
- **R6 — Create round-trip.** Name encoding is injective; risks are (a)
  inconsistent fixture rows (success/address mismatch — audited stage 1c§5),
  (b) the recorded initCode-is-not-bytecode transcript residue (documented,
  gas-like, deferred), (c) `answerCreate` keying drift vs
  `lookupContractCreation?` (mitigate: `answerCreate` *calls*
  `lookupContractCreation?`, no reimplementation).
- **R7 — Gas-key erasure at the Stmt site** (no-gas vs `{gas: gasleft}`
  indistinguishable after `requestedGas` erasure): pre-existing recorded
  limitation from sub-step-1a; stage 1b extends it to the high-level call
  site — extend the DECISIONS note, no new mechanism.
- **R8 — The witness/build blind spot** (§0): the harness never builds the
  library, so type-level breaks in witness modules hide behind green
  replays. Mitigation: stage 0 adds `lake build SolidCore` to the smoke
  script (cheap: incremental).
- **R9 — `SolI.run` termination fragility.** Structural recursion through
  the continuation is validated *today*; if the shared `Interaction` ever
  becomes coinductive/quotiented, the fold needs fuel again — and no honest
  Stmt-level bound exists (loops). Record the dependency in `SolI.run`'s
  docstring: "termination depends on `Interaction` being an inductive; a
  representation change upstream must revisit this fold."

## 4. What is explicitly out of scope here (deferred per roadmap)
World-snapshot population (`OpenWorld` in queries stays `default`;
matchers ignore it) and self-storage re-projection; `gasleft` as a
resource query; intra-frame balance accounting. Stage 2's echo-world
default keeps all of these inert exactly as the roadmap prescribes.

## 5. Proof of concept — validated and reverted

Executed during planning, then reverted (`git status` clean; this file is
the only addition). Two builds were run:

1. **Clean HEAD `lake build SolidCore` → RED** (the §0 finding; errors at
   `Witness/Interface.lean:20834/20893`, type mismatch `Except.ok …` vs
   `Source.SolI (Source.Value × Source.Runtime)`).
2. **Stage-0 fix + PoC slice → GREEN** (`✔ [1090/1091] Built SolidCore`).

The PoC slice (a 110-line diff, fully reconstructible from the following +
the code quoted in §1) was exactly:

- `Witness/Interface.lean` 20827/20884: wrap the two evaluator scrutinees
  in `SolI.foldExpr (Expr.orderFuel core + 1) unspecifiedBinaryOrderContext (…)`
  — arms unchanged. (= stage 0.)
- `Interpreter.lean`, after `contextAnswer` (1988): `SolI.run` (fuel-free
  structural fold — **termination accepted by Lean**, the key uncertainty)
  and `SolI.caught` (the `tryCatch` reification helper) — verbatim as in §1.
- `Interpreter.lean` 7505: `FunctionDef.call : … → Option (SolI CallResult)`
  (degenerate `pure` tree while `Stmt.eval` is still folded) +
  `FunctionDef.call?` redefined as the `SolI.run`-adapter — the exact
  stage-1 adapter shape. Everything above (Checked.lean wrappers, ABI,
  witness modules, the manifest-facing entry points) compiled unchanged.
- `Interpreter.lean` 7553: the theorem simp-set extension quoted in
  stage 1 §4 — the proof closes.

This validates, end-to-end: the fuel-free fold's termination, the
`caught`/`tryCatch` typing, the adapter pattern that freezes every
signature above `FunctionDef.call?`, and the one theorem repair. It is the
verbatim starting point for stage 1 (drop the "degenerate tree" comment
once `Stmt.eval` returns real trees).
