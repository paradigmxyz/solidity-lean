# Function-boundary refactor plan: preserve internal calls in the Solidity core

Status: design, 2026-07-06. Read-only planning artifact (no source edits made).
Follows the decision recorded against `docs/compile-to-yul-readiness.md` §3/D1:
**the internal-function-call boundary WILL be preserved in the Solidity core.**
Rationale: (a) it fixes a real semantic gap — see §1.4, recursion and deep call
graphs currently fail elaboration and are silently *rejected* though solc
accepts them; (b) it gives the future Sc (calling-convention) lowering layer an
actual source IR. So this is a correctness fix with composition payoff, not a
speculative interface.

All `file:line` anchors are as of this read; `Interpreter.lean`, `Checked.lean`,
and `Interface.lean` are under concurrent edit (Phase 5 / A1), so declaration
names are the stable reference. **Implementation must not start until Phase 5
merges** (§5).

---

## 1. Precise current state (verified, not assumed)

### 1.1 What is inlined today, and how

**Everything with internal linkage is inlined at elaboration; modifiers are
inlined by placeholder substitution.** Verified paths in `Interface.lean`:

- **Inline-depth budget.** `defaultInternalCallInlineFuel := 64`
  (`Interface.lean:10111`) is an *elaboration-time inline-expansion-depth*
  budget, not a runtime bound. It is consumed at four entry sites
  (`:14662, :16533, :18137, :18182`), all feeding
  `functionExpandModifiersToCoreWithInternalCalls?`/`…Full?`, and decrements
  once per nesting level of inlined call (`FunctionDecl.internalCallParts?`
  `:10383` matches `internalFuel = fuel + 1`, recurses into the callee body at
  `fuel`, `:10434/:10489`).
- **Internal-call splicing.** `internalCallParts?` resolves the callee **by
  name with argument-based overload selection**
  (`findInternalCalleeWithArgs?` `:8780`), names fresh mangled locals
  (`_arg*`, `_ret_<name>_*`, `:10393/:10401`), α-renames the callee body onto
  them (`Stmt.renameIdents` `:10415`), recursively elaborates it at
  `internalFuel−1`, and splices it as
  `prefixCore ++ [Stmt.captureReturn returnNames bodyCore]`
  (statement form `internalStatementCallCore?` `:10500/:10514`;
  single-return-expression form `internalSingleReturnCallCore?` `:10519`,
  appending a use of the return temp). An internal call site becomes:
  *declare arg/return temps → run the callee body inline → capture its
  `return` into the temps → use them.*
- **Modifier expansion (separate mechanism).**
  `functionExpandModifiersToCoreWithInternalCallsFull?` (`:15026`) folds
  modifier invocations outside-in; `modifierApplyToCoreWithInternalCalls?`
  (`:14998`) binds modifier arguments (`modifierParamBindingsWithArgs?`
  `:15009`) and substitutes the modified function's body at the `_`
  placeholder (`Stmt.toCoreWithInternalCallsReplacingModifierPlaceholder?`
  `:15020/:14985`). Modifiers never become functions.
- **All internal-linkage call kinds share the splicing path**: free functions
  (`internalCallParts?` falls through contract `functions` to `freeFunctions`,
  `:10443`); internal library functions (rewritten to mangled internal names
  `__library_<Lib>_<f>` by `FunctionDecl.rewriteLibraryInternalCalls` `:16448`
  / `libraryHelperName` `:15060`, then inlined as ordinary internal calls);
  `using`-for bound methods (`Stmt.expandUsing` at `FunctionDecl.toCore?`
  `:16497` rewrites `x.foo()` to the internal/library call, then inlined);
  `super`/base calls (`rewriteSuperCalls`/`rewriteBaseCalls` `:16513/:16515`
  → super-helper functions, then inlined).

### 1.2 What call machinery already exists (`Interpreter.lean`)

The interpreter is **not** "fully inlined" in the sense of having no call
machinery — it has exactly **one real frame: the entry frame**, and the
machinery that builds it is reusable:

- `FunctionDef` (`:7700`): `name`, `selector?`, `payable`, `params`,
  `paramAbiCleanups`, `returns`, `body : Stmt` — flat; `body` contains all
  spliced callees; no reference to other functions.
- Entry-frame construction: `initialFrame?` (`:7739`, default-binds
  params+returns), `entryInitialFrame?` (`:7749`, + payable check),
  `evalBodyEntry` (`:7818`: `locals := [frame]` — **one frame per
  external/ABI/checked/constructor entry**), exit normalization
  `callBodyResult` (`:7787`: `normal`→collect named returns
  (`collectReturns` `:7756`); `returned values`→coerce; `selfdestructed`→
  `returned []`; `reverted`→`CallResult.reverted` with the **pre-call state
  snapshot** (rollback); `broke`/`continued`→`reverted typeMismatch`).
- **Who calls `FunctionDef.call?`/`call` — only entry paths, confirmed by a
  full caller sweep**: `Checked.lean:229,242,323,342,361` (checked entries),
  `ABI.lean:598,635,684,883,900,928` (selector dispatch + Phase-5 tree twins),
  `Interpreter.lean:7979/8024` (`Contract.call`/`call?`), `Interface.lean:18851`
  (constructor path) and `:19289–19308` (test wrappers). **No caller is inside
  the `Stmt.eval`/`Expr.eval` mutual block** (block ends `:7663`; all callers
  are after it). The evaluator never constructs a frame.
- `Stmt.captureReturn` evaluation (`Stmt.eval` `:7245`) — the mechanism a real
  frame replaces: runs the spliced body **in the same `runtime`** (no frame
  push; isolation is by α-renaming only), rewrites the callee's
  `Result.returned` into local writes + `Result.normal`, and **passes
  `broke`/`continued`/`reverted`/`selfdestructed`/`normal` through unchanged**.
  The `broke`/`continued` passthrough would be a fidelity bug for an isolated
  frame (a callee must not break the caller's loop); it is safe today only
  because a well-typed callee body has no top-level break/continue.
- Locals model: `Frame := List (String × Value)` (`:816`),
  `LocalEnv := List Frame` (`:817`); `pushScope`/`popScope` (`:948/:951`)
  prepend/drop; **`lookup?`/`assign?` walk all frames** (`:837/:844`) — nested
  block scoping with outer visibility, *not* isolation. A real call frame must
  **replace** `runtime.locals` with a fresh isolated env (e.g. `[calleeFrame]`)
  and restore the caller's env afterward; `pushScope` alone would leak caller
  locals into the callee.
- Phase-5 state (in-flight): `Stmt.eval` + loop companions return
  **`SolI Result`** (`:7563` region; `fuel = 0 → throw SolidityFailure.outOfFuel`
  `:7576/:7601/:7636`); `evalBodyEntry : Option (SolI Result)` (`:7818`),
  `FunctionDef.call : Option (SolI CallResult)` (`:7832`), `call?` folding via
  `SolI.run` (`:7841`). So in-monad recursion threads through the same `SolI`
  the evaluator already uses — no new monad.
- **The function table is not reachable from the evaluator today**:
  `Contract.functions : List FunctionDef` (`:7913`) with
  `findFunctionByName?`/`findCallableFunctionByName?`/`findFunctionBySelector?`
  (`:7938/:7942/:7947`) exists, but `Contract.context` (`:7916`) does not put
  it in `Context`, and nothing inside the eval block can see it.

### 1.3 The core language has no internal-call construct

`Source.Expr` (`:4598`) external-effect constructors: `lowLevelCall` (`:4649`),
`contractCreate` (`:4651`), precompile helpers `externalHash`/`ecrecover`
(`:4654/:4655`). `Source.Stmt` (`:6345`): `tryExternalCall` (`:6386`),
`tryContractCreate` (`:6390`). **No internal-call or function-reference
constructor anywhere.**

### 1.4 The gap, stated exactly (correcting an earlier framing)

At `internalFuel = 0`, `internalCallParts?` falls back to
`functionExpandModifiersToCoreWithStorageRefsOnly?` (`:10430`), which elaborates
the callee body *without* further internal-call expansion; its catch-all
`| other => Stmt.toCore? …` (`:9862`) reaches `Expr.toCore?`'s final
`| _ => none` (`:5744`) on a residual internal call. The `none` propagates and
**the whole contract fails to elaborate**. So: **recursive internal functions
and static call-nesting deeper than 64 are not mis-executed — they are silently
rejected** (`toCoreContract?` = `none`) while solc accepts them. This is an
*acceptance* gap (legal programs refused), which is in some ways worse than a
mis-execution: nothing observable ever runs, so no differential lane has caught
it. Until this refactor lands, it should be a **recorded semantic gap** in
`ROADMAP.md`'s registry (see §6 stage 0 and §8).

### 1.5 solc's behavior, confirmed (the internal/modifier split)

- **Modifiers: substitution semantics; codegen varies.** The Solidity docs
  specify the `_` placeholder as "where the body of the function being modified
  should be inserted" — the *semantics* is body substitution: multiple modifiers
  nest outside-in in declaration order, modifier arguments are evaluated at the
  wrapping site, and `_` may occur multiple times (body inserted at each) or
  zero times (body never runs; function returns default values). Virtual/
  override modifiers resolve to one concrete modifier body per contract before
  expansion. How that substitution is *lowered* is codegen-specific: legacy
  codegen inlines the modifier body at each placeholder, whereas via-IR (the Yul
  pipeline) may emit the modifier's inner body as per-layer Yul helper functions
  — an emission choice, not a change to the substitution semantics. Sources:
  docs.soliditylang.org Contracts §"Function Modifiers", internals/optimizer
  (IR codegen). **Decision: modifiers stay inlined in this semantics** (the
  substitution model, matching solc's meaning), and
  the current placeholder-substitution machinery (§1.1) is kept, including its
  handling of arguments (`modifierParamBindingsWithArgs?`) and inheritance
  (virtual/override resolved during linearization before expansion). Edge cases
  the kept machinery must be checked against (stage-2 audit, §6): multiple `_`
  (body inlined per placeholder — after this refactor the body contains *call
  nodes*, so double insertion no longer duplicates whole callee bodies, only
  call sites — a size/perf win, semantics unchanged); zero `_` (body dropped,
  named returns default — verify current behavior matches); modifier arguments
  evaluated once, before the first placeholder, in the wrapping scope.
- **Internal functions: solc emits real functions.** In the IR (Yul) pipeline,
  internal Solidity functions become internal Yul functions (the optimizer may
  *later* inline small ones — an optimization, not the semantics), which is why
  recursion works in solc. Free functions, internal library functions, and
  `using`-for bound methods likewise compile to internal Yul functions
  (delegatecall only applies to *external* library calls). **Decision: all four
  internal-linkage kinds get the boundary** — they already flow through the
  single `internalCallParts?` path (§1.1), so the boundary is uniform for free.
  `super`/base helper calls are internal dispatch resolved at elaboration
  (C3-linearized); they also get the boundary (they are ordinary internal
  functions after the rewrite at `:16513`).

---

## 2. Target core representation

### 2.1 New core constructs

One new **statement** node and no new expression node (rationale in §3.2):

```
-- in the Source.Stmt inductive (Interpreter.lean ~:6345)
| internalCall
    (targets : List String)     -- caller locals receiving the results (may be [])
    (callee  : String)          -- RESOLVED, mangled, overload-unique table key
    (args    : List Expr)       -- argument expressions, caller scope
```

- `callee` is the elaboration-resolved name (overload selection, library
  mangling `__library_<Lib>_<f>`, super-helper names all happen at elaboration
  exactly as today — the node carries the *result* of that resolution, keeping
  the core monomorphic like every other core construct).
- Expression-position internal calls are **hoisted by elaboration** into
  statement position with fresh temps (§4.2), preserving evaluation order.
  This mirrors solc's IR codegen (expressions with calls are sequentialized)
  and keeps the Expr layer's control-flow regime unchanged (revert-only), for
  the same reason the Phase-5 plan chose its model A: no second control-flow
  regime inside the expression evaluator.

### 2.2 The function table

`Contract.functions : List FunctionDef` already *is* the table (`:7913`). What
is missing is evaluator access. **Definition-order constraint (real, verified):**
`Context` (`:1488`) is defined long before `Stmt` (`:6345`) and `FunctionDef`
(`:7700`), and `FunctionDef.body : Stmt`, so the table cannot live in `Context`
without reordering thousands of lines. **Design: thread the table as a new
explicit parameter of the eval mutual block** instead:

```
-- defined immediately after the Stmt inductive, before the eval block:
structure InternalFunction where
  name    : String
  params  : List BindingDecl
  returns : List BindingDecl
  body    : Stmt

abbrev FunctionTable := List InternalFunction   -- lookup by name

-- the mutual block gains one parameter:
Stmt.eval  : Nat → FunctionTable → Context → Runtime → Stmt → SolI Result
Expr.eval… : (unchanged — no internal calls at Expr level)
```

`FunctionDef` (which additionally carries `selector?`, `payable`,
`paramAbiCleanups` — entry-only concerns) gains a projection
`FunctionDef.toInternal : FunctionDef → InternalFunction`, and
`Contract.table : FunctionTable := contract.functions.map (·.toInternal)`.
`FunctionDef.call`/`evalBodyEntry` pass `contract.table` down. (Alternative
rejected: move `FunctionDef` above the eval block and use it directly — more
churn, mixes entry-only fields into the internal-call path; the small
projection is cheaper and keeps the entry/internal distinction explicit.)

### 2.3 Recursion bound: the existing statement fuel, not a new one

No new fuel. The eval block is already fuel-indexed with
`fuel = 0 → throw SolidityFailure.outOfFuel` (`:7576`). An `internalCall` arm
recurses into the callee body via `Stmt.eval (fuel − 1) table …` — internal
call depth is thereby bounded by the entry fuel exactly like loop iterations
already are, and exhaustion is the **same reflectable `outOfFuel`** Phase 5
introduced, which is precisely the truncation arm `ForwardRel.trans`'s
`hReflect` needs (readiness doc §0). The inline-fuel-64 constant is deleted
with the splicing path (§6 stage 4). Faithfulness note: solc has no such bound
(real recursion is gas-bounded); our fuel bound is a *truncation*, reflected as
`outOfFuel` — the standard fuel-semantics posture this repo already takes for
loops, now uniform for calls. Harness impact: entry fuel is already sized
generously; corpus programs are shallow. (§7 R2.)

### 2.4 CoreContract before/after

```
BEFORE (today)                          AFTER
Contract                                Contract                (unchanged shape)
  functions : List FunctionDef            functions : List FunctionDef
    body = one flat Stmt with EVERY         body = the function's OWN statements;
    internal/free/library/using/super       internal-linkage calls are
    callee spliced in via captureReturn     Stmt.internalCall nodes keyed into
    (modifiers also expanded in)            the SAME functions list (via .table);
                                            modifiers still expanded in
  -- recursion: unrepresentable           -- recursion: representable, fuel-bounded
  -- body size: O(inlined closure),       -- body size: O(own statements);
     duplicated per call site                each function elaborated ONCE
```

Note the table must now also contain internal-only functions that today never
appear as `FunctionDef`s (they only existed spliced into callers): elaboration
emits a `FunctionDef` (with `selector? := none`) for every reachable
internal-linkage function — contract-internal (post-linearization), free,
library-internal (mangled name), and super-helpers. Dispatch is unaffected:
`findFunctionBySelector?` (`:7947`) only sees selector-bearing entries.

---

## 3. Interpreter execution model

### 3.1 The `internalCall` arm (in-monad, NOT a query)

**Coordination-critical:** internal calls stay **inside** the `SolI` monad —
they are *not* `Query.external` emissions. The roadmap's alphabet decision is
explicit (internal calls, free functions, internal library calls, bound
`using` methods stay internal; only external calls/creates/precompiles emit),
and the Yul side agrees: internal Yul function calls in
`Yul.Source.Canonical.call` (`evm-compiler Yul/EffectSemantics.lean:159`) run
with fresh var frames and emit nothing. The transcript of a Solidity execution
must therefore be invariant under this refactor — same queries before and
after. That is also the behavior-preservation argument (§6).

Evaluation of `Stmt.internalCall targets callee args`, composed from existing
pieces:

```
1. Evaluate args left-to-right per effectiveChildEvalOrder discipline
   (same as every other statement's operands), in the CALLER's runtime,
   via the existing Expr evaluation (`.caught` where the site expects
   value-or-revert, exactly like current statement operand sites).
2. Look up callee in the FunctionTable. Miss → throw (.revert typeMismatch).
   (Static absence should be impossible for elaboration-produced cores —
   elaboration built the table — but the interpreter stays defensively total,
   matching its existing style.)
3. Build the callee frame: initialFrame?-style default binding of
   params := arg values (coerced as the entry path does) and returns :=
   defaults. Frame-isolation step: savedLocals := runtime.locals;
   calleeRuntime := { runtime with locals := [frame] }   -- REPLACE, not push
   (state — storage/memory/events/transient — is shared: EVM internal calls
   share the memory/storage of the frame; only locals are private).
4. result ← Stmt.eval (fuel − 1) table context calleeRuntime fn.body
   -- same SolI; recursion is just this recursive occurrence; outOfFuel
   -- propagates as the monadic throw it already is.
5. Map the callee body Result (the internal-call analog of callBodyResult,
   producing caller-runtime updates instead of a CallResult):
   | returned r values  → coerce values to fn.returns (same coercion as
                          callBodyResult), restore locals := savedLocals
                          (keeping r.state), assign to targets → Result.normal
   | normal r           → collectReturns fn.returns from r's frame (named
                          returns), then as above
   | reverted r err     → pure (Result.reverted r err)
                          -- propagates; outer statement/entry rollback
                          -- discipline is unchanged (rollback happens at
                          -- CallResult construction from the entry snapshot,
                          -- and at try/catch sites — internal reverts
                          -- propagate exactly as an inlined body's revert
                          -- Result did today)
   | selfdestructed r   → pure (Result.selfdestructed r) -- halts the whole
                          -- external call frame, propagating through callers,
                          -- until callBodyResult maps it (`:7787`) — matches
                          -- EVM SELFDESTRUCT halting the contract execution
   | broke r / continued r → pure (Result.reverted r typeMismatch)
                          -- a callee CANNOT break the caller's loop; this
                          -- mirrors callBodyResult's treatment and FIXES the
                          -- latent captureReturn passthrough noted in §1.2
```

Locals restoration detail: the callee's `Runtime` carries both `state` and
`locals`; step 5 must take the *callee's* final `state` (storage/memory/event
mutations are real) and the *caller's* saved `locals`. This is the one place
frame isolation is easy to get subtly wrong — it gets a dedicated witness
(§6 stage 1).

### 3.2 Why a Stmt-level node (and not an Expr-level one)

An Expr-level `internalCall` would have to return `(Value × Runtime)` and can
therefore express only value-or-revert outcomes — but a callee can
`selfdestruct` (must halt the whole frame, not produce a value), and mapping
that into the Expr layer would require either a new `SolidityFailure`
constructor (polluting the shared failure vocabulary Phase 5 just settled) or a
second control-flow regime inside the expression evaluator (exactly what the
Phase-5 plan's model-A analysis rejected, `docs/phase5-propagation-plan.md` §1).
Statement-level calls compose with the six-way `Result` for free. The cost is
elaboration-side hoisting of expression-position calls (§4.2) — real but
principled work that solc's own IR codegen also performs, and which the current
elaboration *already half-does* (`internalSingleReturnCallCore?` already
sequentializes single-return expression calls into statements + a temp use,
`:10519`; hoisting generalizes the existing mechanism rather than inventing
one).

### 3.3 try/catch is unaffected

`try` applies only to external calls and contract creation (Solidity language
rule; core nodes `tryExternalCall`/`tryContractCreate` `:6386/:6390`, both
environment-answered). A `try` target is never an internal call, so the frame
model does not interact with catch dispatch. Internal calls *inside* a try'd
expression's operands or inside catch blocks are ordinary hoisted statement
calls. (§7 R5 records the residual check.)

---

## 4. Elaboration and typechecker changes

### 4.1 Elaboration: emit call nodes + table instead of splicing

- `FunctionDecl.internalCallParts?` (`:10383`) stops splicing: it keeps its
  resolution work (callee lookup `findInternalCalleeWithArgs?`, overload
  selection, arg elaboration) but emits
  `Stmt.internalCall targets mangledName argsCore` instead of the α-renamed
  body splice. The `_arg*`/`_ret_*` mangling and `renameIdents` machinery for
  *callee bodies* becomes unnecessary (frame isolation replaces α-renaming);
  temp naming survives only for expression-position hoisting (§4.2).
- **Table construction**: `ContractDecl.directCoreFunctions?` (`:18036`) /
  `toCoreFromOrders?` (`:18195`) additionally elaborate every internal-linkage
  function *once* into a `FunctionDef` with `selector? := none`: post-C3
  contract-internal functions, `freeFunctions`, library-internal functions
  (under their `__library_*` mangled names), and the super-helper functions the
  rewrites at `:16513/:16515` produce. Each such function's *own* body is
  elaborated with call nodes (this is now a plain map over functions — the
  recursive inline closure, and the fuel, disappear). The existing
  reachability set is exactly "what the current inliner could reach", so no
  new name-resolution machinery is needed — the same resolvers now run once
  per function instead of once per call site.
- **Modifiers: unchanged.** The placeholder-substitution cluster
  (`:14985–15026`) is kept verbatim; it now substitutes a body whose internal
  calls are nodes, so modifier expansion no longer multiplies inlined callee
  closures (a size win; semantics identical). The modifier edge cases in §1.5
  get an explicit audit + witnesses in stage 2.
- **Recursion becomes representable**: the per-function elaboration has no
  inline recursion, so `defaultInternalCallInlineFuel` and the
  `toCoreWithStorageRefsOnly?` fallback path (`:10430`, `:9785–9862`) are
  deleted in stage 4. Mutual recursion works because the table is closed over
  all functions before any body needs it (name-keyed, late-bound at eval).

### 4.2 Expression-position hoisting

Elaboration sequentializes expression-position internal calls into statement
position, preserving the deterministic child evaluation order:
- Plain subexpression: `y = f(a) + g(b)` → temps `t1 := call f; t2 := call g;
  y = t1 + t2` **in the effective child order** (the same
  `effectiveChildEvalOrder` the evaluator applies, so observable order is
  unchanged — this must be stated and witnessed, §6 stage 3).
- Short-circuit operands (`&&`/`||`), ternary branches: hoist into nested
  `if` statements so a call in the unevaluated branch does not execute.
- Loop conditions with calls: rewrite `while (cond)` →
  `loop { t := cond-with-calls-hoisted; if (!t) break; body }` (and the `for`
  analog) — the standard sequentialization, matching solc IR.
- `internalSingleReturnCallCore?` (`:10519`) is the existing template for the
  plain case; the short-circuit/ternary/loop-condition cases are new
  elaboration work and are the riskiest part of stage 3 (§7 R4).

### 4.3 Typechecker: nearly untouched

`TypeCheck.lean` checks the *surface* and produces only accept/reject
(`CheckedSourceUnit = { source }`, `TypeCheck.lean:12116`); it never sees core
call nodes. It already resolves call targets for checking purposes. Recursion
was never rejected by the typechecker — the rejection lived in elaboration's
inline fuel — so no acceptance-lane change is expected from TypeCheck. One
audit: confirm no typechecker rule *depends* on inline-ability (none found in
the current sweep; the checker has no knowledge of the inliner).

---

## 5. Coordination and sequencing (hard constraints)

- **Blocked on Phase 5 merging.** This refactor rewrites the same regions the
  Phase 5 agent is actively editing: the `Stmt.eval` mutual block signature
  (adding the `FunctionTable` parameter), `FunctionDef.call`/`evalBodyEntry`
  (passing the table), and `Interface.lean`'s elaboration driver (which A1's
  `NumberRat` work also touches). Starting before Phase 5's stages 2–3 land
  would produce unmergeable conflicts in `Interpreter.lean` and re-litigate
  the monad plumbing. **Do not start until the Phase 5 tree is committed and
  the full replay is green**; design above is stated against the post-Phase-5
  shape (SolI-returning eval block, `?`-adapters, scripted responders).
- The plan *benefits* from Phase 5: the in-monad recursion (§3.1) needs
  `Stmt.eval : … → SolI Result`, which Phase 5 stage 1 already delivered.
- **Transcript invariance is the coordination contract with Phase 5's
  responders**: internal calls emit no queries, so every fixture's scripted
  responder sequence is untouched by this refactor. Any responder diff during
  implementation is a bug in the refactor, full stop.
- A1 (`NumberRat`) is orthogonal in content but co-located in
  `Interface.lean`; sequence after it merges to keep diffs reviewable.
- Manifest neutrality: entry-point names/signatures (`FunctionDef.call?`,
  `Contract.call?`, ABI/Checked entries) do not change; the ~119 witness defs /
  419 evals reference only those. Expected manifest diff: **zero**.

---

## 6. Staged plan (each stage buildable; corpus green; one commit per stage)

Gates per stage: `lake build SolidCore` + `scripts/smoke_replay.sh`; full
replay (`compare_forge_solc_interpreter.sh`, cases=98) at the marked stages.
Behavior-preservation argument used throughout: for programs the current
elaboration accepts, inlined-body execution and framed execution compute the
same states/results — the callee body is the same core code, run against the
same `state`, with locals isolation replacing α-renaming (which already
guaranteed non-interference), and the transcript is unchanged because internal
calls emit nothing. The corpus is the arbiter; any divergence is a latent bug
to pin first (roadmap rule).

- **Stage 0 — record the gap + pin it with a differential lane.**
  Add the ROADMAP gap-registry entry (recursion/deep-nesting silently rejected
  at elaboration; solc accepts — §1.4). Add one paired Forge lane: a contract
  with (a) a genuinely recursive internal function (e.g. naive factorial/fib
  with small input) and (b) a static call chain deeper than 64. solc/Forge
  side: green today. Lean side: **expected-fail today** (elaboration `none`),
  recorded as the pinned-bug lane per the corpus freeze policy ("new lanes only
  to pin a discovered bug" — this is that). This lane is the regression guard
  that flips green at stage 5. Full replay (unchanged expectations elsewhere).
- **Stage 1 — core node + table + evaluator arm (dead code).**
  Add `Stmt.internalCall`, `InternalFunction`/`FunctionTable` (defined after
  `Stmt`, §2.2), the eval-block parameter, and the `internalCall` arm (§3.1);
  `FunctionDef.toInternal`; `Contract.table`; thread the table through
  `evalBodyEntry`/`call`/entry adapters (types only — no elaboration produces
  the node yet, so corpus-neutral by construction). Add targeted `#eval`
  witnesses (e2e-proofs lane style, not the frozen corpus): direct-recursion
  via a hand-built table; locals isolation (callee cannot read caller locals;
  caller locals intact after); state sharing (callee storage/memory writes
  visible after); `broke`-in-callee → `reverted typeMismatch`;
  `selfdestructed` propagation; fuel-0 call → `outOfFuel`. Risky bit: the
  eval-block signature change touches every recursive call site in the mutual
  block — mechanical, `--word-diff`-reviewable. Build + smoke.
- **Stage 2 — elaboration emits call nodes for contract-internal + free
  functions; modifier audit.**
  Switch `internalCallParts?` to node emission for the contract-internal and
  free-function resolution paths (statement-position calls and the
  single-return expression form it already sequentializes); build the table in
  `directCoreFunctions?`. Modifier expansion untouched — but run the §1.5
  modifier edge-case audit here (multiple `_`, zero `_`, args-evaluated-once,
  virtual/override), adding a witness per edge case. **Full replay** (this is
  the big behavior-preservation checkpoint; the smoke set's
  internal-call-heavy lanes first).
- **Stage 3 — expression-position hoisting; library/using/super linkage.**
  Generalize hoisting (§4.2: short-circuit, ternary, loop conditions) and
  switch the library-internal, `using`-for, and super-helper paths to node
  emission. This is the riskiest elaboration stage (evaluation-order
  fidelity); the order-sensitive witnesses (`unspecifiedBinaryOrderEval`
  family) and the OZ/solmate corpus lanes are the sentinels. **Full replay.**
- **Stage 4 — delete the splicing machinery.**
  Remove the inline-splicing path in `internalCallParts?`, the
  `toCoreWithStorageRefsOnly?` fallback (`:10430`, `:9785–9862`),
  `defaultInternalCallInlineFuel` (`:10111`) and its four consumption sites,
  and the callee-body α-renaming (`renameIdents` use at `:10415`; keep the
  function itself if modifiers/hoisting still use it). `captureReturn` stays —
  it is still the modifier-expansion and hoisting mechanism — but no longer
  receives whole callee closures. Build + smoke; grep-gate: zero references to
  the inline path.
- **Stage 5 — flip the recursion lane green; close the gap.**
  The stage-0 lane's Lean side now elaborates and runs; assert the paired
  Forge equality (factorial value, deep-chain result). Update the ROADMAP gap
  registry (gap closed), `docs/DECISIONS.md` entry, and the readiness doc's D1
  (Sc now has a source IR). **Full replay + wall-clock comparison** vs the
  pre-stage-1 baseline (§7 R1's measurement point).

---

## 7. Risk register

- **R1 — Performance.** Two opposing effects: frames add per-call allocation
  (frame build, locals save/restore) but elaboration stops duplicating callee
  closures per call site (today a hot helper is re-elaborated and re-executed
  as spliced code at *every* call site, and modifier expansion multiplies it) —
  core bodies shrink, and the heavy OZ lanes (minutes today) plausibly get
  *faster*. Measure at stages 2/3/5 (smoke wall-clock) and the stage-5 full
  replay vs baseline; the roadmap's ~2× rule applies. No fusion machinery is
  expected to be needed (no new monad, no new fold).
- **R2 — Fuel-semantics shift.** Today an inlined callee's statements consume
  the caller's statement fuel *as body depth*; after, a call consumes one fuel
  unit and the callee gets `fuel − 1` as a fresh depth allowance. Programs near
  the fuel horizon could flip between `outOfFuel` and completion. Invisible to
  the corpus (entry fuel is generous, `outOfFuel` folds to `none` at the
  adapters), but it changes the *truncation boundary* the future composed
  theorem quantifies over. Record the new fuel discipline (fuel = statement
  recursion depth, uniform for loops and calls) in `docs/DECISIONS.md`; do not
  attempt to preserve the old inline-fuel horizon (it was an elaboration
  artifact, not semantics).
- **R3 — `Result`/control-flow interaction at the frame boundary.** The §3.1
  mapping must match `callBodyResult` field-for-field (returns coercion,
  named-return collection, revert passthrough) or framed execution diverges
  from today's inlined execution on exactly the subtle cases (named returns
  assigned then `return;`, empty `returned []` with non-empty declared
  returns…). Mitigation: implement the mapping by *refactoring
  `callBodyResult`* into a shared core both the entry path and the
  internal-call arm call (single source of truth), plus the stage-1 witnesses.
  The `broke`/`continued → reverted typeMismatch` choice *changes* the
  captureReturn passthrough behavior (§1.2) — unreachable for well-typed
  callees, but if any corpus case diverges here it is a latent bug to pin, not
  to paper over.
- **R4 — Evaluation-order fidelity of hoisting (stage 3).** Hoisted temps must
  reproduce `effectiveChildEvalOrder` (right-to-left Yul-compatible) exactly;
  short-circuit and ternary hoisting must not execute calls in unevaluated
  branches. This is where a silent order regression would hide. Sentinels: the
  order witnesses and revert-order corpus lanes; add one targeted witness per
  hoisting shape (binary, short-circuit, ternary, loop condition).
- **R5 — try/catch.** Try targets are external-only (§3.3), so no direct
  interaction — but stage-3 hoisting must handle internal calls appearing in
  the *operands* of a try'd external call (value/gas options, argument
  expressions) by hoisting them *before* the try statement, preserving order
  relative to the external call's own operand evaluation. One witness.
- **R6 — Library/`using`/`super` mangling drift.** The table keys must be
  byte-identical to the names the call-site rewrites produce
  (`__library_*`, super-helper names). Mitigation: both sides use the same
  helper (`libraryHelperName` `:15060`) — enforce by construction, not
  convention; grep-gate at stage 3. Note external (public) library calls are
  *not* internal linkage — they remain `delegatecall` queries (roadmap
  alphabet decision) and are out of scope here.
- **R7 — Frame isolation leaks.** Replacing `runtime.locals` (not pushScope)
  is load-bearing (§1.2 B9); getting it wrong leaks caller locals into the
  callee (visible only to programs that shadow — the α-renaming era made this
  unobservable, so the corpus may not catch a leak). Stage-1 witnesses cover
  it directly (callee referencing an undeclared name that exists in the
  caller must revert `typeMismatch`, not resolve).
- **R8 — Elaboration blast radius in `Interface.lean`.** `internalCallParts?`
  sits inside the largest elaboration cluster (~10.1k–16.5k) with four
  callers; stage 2/3 touch it while keeping the modifier machinery byte-stable.
  Mitigation: stage split by linkage class, full replay at 2 and 3, and the
  stage-4 deletion only after both replays are green.
- **R9 — Silent scope change in acceptance.** After stage 4, contracts that
  previously failed elaboration (recursion, deep nesting) now elaborate. That
  is the *point* — but it widens the accepted set, so the acceptedness lanes
  (~309 rejection lanes) must be replayed to confirm no rejection lane was
  accidentally relying on inline-fuel failure (none should — they are
  typechecker lanes — but verify; full replay covers it).

---

## 8. Interim posture (until this lands)

Until stage 5, the recursion/deep-call-graph rejection is a **genuine recorded
semantic gap**: legal Solidity (accepted by pinned solc) that this semantics
silently refuses to elaborate. It should be entered in `ROADMAP.md`'s
"Known semantic gaps" registry at stage 0 (or immediately, at the
orchestrator's discretion — the registry edit is independent of this plan's
implementation), phrased approximately:

| Gap | Status | Notes |
| --- | --- | --- |
| Internal-function recursion / call-nesting > 64 | Open — fix planned (`docs/function-boundary-refactor-plan.md`) | Elaboration inlines all internal-linkage calls with `defaultInternalCallInlineFuel = 64` (`Interface.lean:10111`); residual calls at fuel 0 make `toCoreContract?` return `none`, silently rejecting programs solc accepts. Fix = preserve the function boundary (call nodes + function table + framed in-monad calls); also gives the future Sc lowering layer its source IR. |
