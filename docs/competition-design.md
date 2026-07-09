# Divergence Contest — Design (coverage + soundness lanes, exclusion gate)

**Status:** design, decisions made. **Scope:** a public, for-fun contest where
entrants submit Forge tests that demonstrate a divergence between **Solidus**
(this repo's executable Lean Solidity 0.8.35 semantics) and real **solc 0.8.35 /
Foundry-EVM**. Qualifying submissions earn a place on a public leaderboard; there
is no monetary component. The adjudicator is fully programmatic so counterexamples
can be checked automatically on submission.

This document is the plan of record: the versioned exclusion register with
machine-checkable detectors, the reject-gate pipeline, the recommended
multi-contract execution model with a feasibility argument grounded in the
existing responder code, the two-lane adjudication decision tree, the submission
format and harness pipeline, anti-gaming/dedup/scoring, and a phased build plan.

It is grounded in the actual repo: the importer guard
(`scripts/solc_ast_to_lean_source.py` `guard_no_unsupported_nodes`, line 416, and
the `EXCLUDED_NODE_TYPES` / `SUPPORTED_NODE_TYPES` / `SOURCE_SCALAR_VALUE_DOMAINS`
tables, lines 34–69); the harness Forge-vs-Solidus flow
(`scripts/run_forge_interpreter_harness.py`); the open-world responder/postWorld
model (`SolidCore/Solidity/Interpreter.lean` `ScriptedResponder.answer`/`answerCall?`,
`SolI.runWith`/`runFailOpen`, `snapshotWorld`/`adoptWorld`, `Contract.callCalldata*`
in `ABI.lean`); and the deferred-gap registries in `ROADMAP.md` (~line 458),
`docs/solidity-feature-coverage.md`, `docs/solidus-solc-deep-comparison.md`
(G1–G22), and `docs/solc-implementation-divergences.md`.

---

## 0. What "divergence" means here

Solidus is a source-level semantics with an **open-world interaction model**.
It imports a solc AST into Lean (`solc_ast_to_lean_source.py`), type-checks
(`TypeCheck.lean`/`Checked.lean`), elaborates (`Interface.lean`), and executes
(`Interpreter.lean`). External calls and creates become `Query.external` nodes
carrying a real `OpenWorld` snapshot (`snapshotWorld`); an **answerer**
(`(q : Query) → Answer q`) supplies each `CallResponse`/`CreateResponse` and its
`postWorld`, which the interpreter adopts wholesale (`adoptWorld`), with the
round-trip law `snapshotWorld (adoptWorld w …) = w` proved in `AdoptionLaws.lean`.

A contest submission is a claim of the form: *"On this program, with this call,
solc+EVM produce observable O, but Solidus produces O′ ≠ O (or Solidus cannot run
the program at all)."* The contest exists because Solidus is validated **only** by
its differential corpus (`tests/forge-harness/manifest.json`, 128 lanes) — it has
no end-to-end soundness theorem — so out-of-corpus divergences are the live risk
the contest is designed to surface and rank on the leaderboard.

The two lanes:

- **COVERAGE-gap lane (lane C).** A legitimate, in-scope Solidity 0.8.35 feature
  that solc accepts + runs, but Solidus **fails closed** on: the importer
  `fail()`s, or type-check/elaboration rejects, or execution cannot proceed.
  Must NOT be an intentional exclusion (see §1).
- **SOUNDNESS-gap lane (lane S).** Solidus **runs** the program to completion but
  produces a **different observable**: wrong return value, wrong revert/panic
  (or revert vs. success), wrong final state/events, wrongly ACCEPTS a program
  solc rejects, or wrongly REJECTS a program solc accepts. The canonical hunting
  ground is the G-register (G1–G22) in `docs/solidus-solc-deep-comparison.md`.

Both lanes require the claimed behavior to be **real on solc+EVM** — the Forge
test must pass against pinned solc 0.8.35 and Foundry-EVM before Solidus is ever
consulted (§4). A submission that misreports what real solc does is invalid.

---

## 1. The exclusion register (canonical, versioned)

The register is the contract between the maintainer and entrants: it enumerates
every place Solidus **intentionally** does not model 0.8.35, so that a rejection
or divergence traceable to one of these is **out of scope**, not a qualifying
gap. It is **versioned** (`REGISTER_VERSION`, semver) and **shrinks** as gaps are
fixed; each submission is adjudicated against the register version in force at its
submission timestamp (§6).

Each entry has: an **ID**, a **precise machine-checkable detector**, a
**syntactic/semantic** classification, and the **reason** it is out of scope.
Detectors run over solc's analyzed AST of **every** submitted source (§2), not
just the entry contract — an adversary will hide an excluded feature in a callee.

### 1.1 Syntactic exclusions (detectable by a pure AST scan)

These are decided by node-type / member-name / directive presence alone. The
detector is a predicate over the solc AST JSON; a single hit anywhere in any
submitted source ⇒ `OUT_OF_SCOPE`.

| ID | Excluded feature | Detector (over solc AST of every source) | Reason OOS |
|---|---|---|---|
| X-ASM | Inline assembly / Yul | any node with `nodeType == "InlineAssembly"` or `nodeType` starting `"Yul"` | `EXCLUDED_NODE_TYPES` (`solc_ast_to_lean_source.py:36`); `ROADMAP.md:469`. Meaning *is* the shared Yul semantics; deferred. |
| X-IMPORT | Imports / multi-file units | any `nodeType == "ImportDirective"`; or `SourceUnit.absolutePath` referencing a non-submitted unit; or >1 `SourceUnit` with cross-unit `ImportDirective` | `EXCLUDED_NODE_TYPES`; `ROADMAP.md:470`. Flattening is the intended preprocessing step. (Multiple contracts in ONE flattened source are allowed — see §3.) |
| X-GASLEFT | `gasleft()` as a distinguishing observable | any `FunctionCall` whose callee `Identifier.name == "gasleft"`; or `MemberAccess.memberName == "gasleft"` | `ROADMAP.md:467/473`. `gasleft` is modeled as a *resource query* answered ambiently, not real gas metering; its value is not a faithful observable. |
| X-MSIZE | `msize` | `msize` only reachable via assembly ⇒ already caught by X-ASM; detector retained for defense-in-depth (any identifier `msize` in an `InlineAssembly` body) | mission brief; no memory-size model. |
| X-GASMEMBER | `.gas(x)` / `{gas: x}` call option **used as an observable** | see §1.2 SEM-GAS — presence of the option is fine; asserting on its *effect* is not | Gas metering OOS (`ROADMAP.md:473`); the call-option is honored structurally but gas is not metered. |
| X-CREATIONCODE | `type(C).creationCode` / `.runtimeCode` used for a bytecode-dependent observable | `MemberAccess.memberName ∈ {creationCode, runtimeCode}` — see §1.2 SEM-CODE for the observable test | Create initCode is source-canonical, not compiled bytecode (`ROADMAP.md:468`). Length/keccak/extcodehash of it are not faithful. |
| X-CREATE2ADDR | create2 address that depends on real init bytecode | `salt` present on a `new C{salt: …}()` **and** the submission observes the resulting address (see §1.2 SEM-ADDR) | create2 address = `keccak(0xff‖deployer‖salt‖keccak(initcode))`; Solidus lacks real initcode (`ROADMAP.md:468`, G22). |
| X-EXTCODEHASH-CREATED | `extcodehash`/`.codehash`/`.code` of a contract **created within the submission** | `.codehash`/`.code`/`.code.length` on an address bound to a `new`-created contract | same root as X-CREATIONCODE: created code has no real bytecode in Solidus. |
| X-FIXED-EXEC | Executable `fixed`/`ufixed` arithmetic | any expression node whose `typeDescriptions.typeString` matches `^u?fixed` and appears as an operand of an arithmetic `BinaryOperation`/`Assignment` | solc **also** rejects executable fixed-point (`fixed-point-boundary` lane confirms both agree); a divergence here is impossible, so submissions asserting one are OOS by construction. |
| X-STORAGELAYOUT | `layout at N` storage-layout specifier | `StorageLayoutSpecifier` node / `storageLayout` at-clause | fail-closed at import (`solc_ast_to_lean_source.py` guard); asm-observed; OOS. |

Implementation note: X-ASM, X-IMPORT, X-STORAGELAYOUT **coincide with Solidus's
own importer guard** — `guard_no_unsupported_nodes` already `fail()`s on
`InlineAssembly`/`Yul*`/`ImportDirective` via `EXCLUDED_NODE_TYPES`. The gate does
not re-implement that classification; it *reuses the same `EXCLUDED_NODE_TYPES`
table* so the register and the importer can never drift (§2, §7).

### 1.2 Semantic exclusions (need a smarter check than node presence)

Here the *feature* is allowed to appear — what is excluded is **asserting on an
observable that Solidus does not intend to model faithfully**. Presence is not a
hit; use-as-a-distinguishing-observable is. The detector is an AST scan for the
feature plus a **taint/flow check**: does a value derived from the excluded
quantity flow into the Forge test's assertion (a `assertEq`/`assertTrue`/expected
return compared by the harness), or into the return value / revert data / event
that the harness treats as the observable (§3.4)?

| ID | Excluded observable | Detector | Reason OOS |
|---|---|---|---|
| SEM-GAS | A test that **asserts a specific gas amount** (`gasleft()` delta, `.gas`-option effect, `tx.gasprice`-derived cost) | X-GASLEFT catches literal `gasleft`. Additionally: taint any subexpression of type `uint256` derived from `gasleft()`/`gasLeft`/`tx.gasprice` and flag if it reaches an assertion or the observed return. | Gas is not metered; any gas-quantity observable is definitionally divergent-but-OOS. |
| SEM-CODE | An observable that depends on **real compiled bytecode** — `type(C).creationCode.length`, `keccak256(type(C).creationCode)`, `runtimeCode`, `address(c).code`, `.codehash` of created code | flag when a `bytes`/`bytes32`/`uint` derived from `creationCode`/`runtimeCode`/`.code`/`.codehash` of a submission-created contract flows to an assertion or observed return | Solidus's initCode is `len‖name‖args` (source-canonical), not EVM bytecode (`ROADMAP.md:468`). |
| SEM-ADDR | An observable that is a **create2 predicted address** (or any address that depends on init bytecode) | flag when the address of a `new C{salt:…}()` result, or a hand-computed `keccak(0xff‖…)` create2 address, flows to an assertion/observed return | create2 address depends on `keccak(initcode)`; Solidus lacks it (G22). Non-salted `new` addresses ARE modeled (`CreateResponse.address`) and are in scope. |
| SEM-CLOSEDGAS | Closed-world gas metering / OOG as an observable | any assertion that a call reverts *specifically due to out-of-gas*, or that distinguishes success/revert by a gas stipend (`.send`/`.transfer` 2300-stipend-driven behavior where the difference is the stipend, not logic) | OOS by the same gas decision; Solidus does not meter the 2300 stipend. |

**How the gate flags each.** Syntactic entries (§1.1) are a one-pass predicate
over `nodeType` / `memberName` / directive presence — cheap, exact, no false
positives. Semantic entries (§1.2) are a two-part check: (a) the feature appears
(same cheap AST predicate), AND (b) a **conservative intra-source data-flow /
taint** pass shows a value derived from the excluded quantity reaching an
**observed** position (the assertion comparands the harness checks, or the entry
call's return/revert/event). Part (b) is deliberately **conservative — it errs
toward OOS**: if a `creationCode`-derived value *might* reach an assertion, the
submission is rejected `OUT_OF_SCOPE` with the specific taint path printed. This is
the correct bias: a false OOS costs one entrant a resubmission with the excluded
observable removed; a false PASS would let an adversary bank a fake divergence.

### 1.3 Register format

The register is a single versioned JSON/py table (`contest/exclusion_register.py`,
`REGISTER_VERSION = "1.0.0"`), each row:

```
{ id, kind: "syntactic"|"semantic", detector: <predicate ref>,
  reason, roadmap_ref, since_version, removed_in_version|null }
```

`removed_in_version` is set (not deleted) when a gap is fixed and the exclusion
retired, so historical adjudications remain reproducible. The syntactic detectors
import `EXCLUDED_NODE_TYPES` directly from `solc_ast_to_lean_source.py` so they
cannot drift from the importer.

---

## 2. The reject gate — pipeline

**Where it runs.** A standalone pass, `contest/reject_gate.py`, that runs
**after** solc has produced the analyzed AST for **all** submitted sources and
**before** Solidus import. It consumes the same solc JSON AST the importer
consumes (pinned solc 0.8.35, `--ast-compact-json`), so it sees exactly what
Solidus would see.

**What it scans.** Every `ContractDefinition` in every `SourceUnit` of the
submission — entry contract, every callee, every library, every base — the whole
transitive closure that solc compiled. It does NOT scan only the contract named as
the entry point. (Rationale in §3: an adversary hides `gasleft()` in a callee to
force a fake value-divergence; whole-submission scanning is the counter.)

**What it outputs.** One of:

- `OUT_OF_SCOPE { register_version, hits: [{id, source, contract, node_src, reason, taint_path?}] }`
  — one or more exclusion detectors fired; the submission is rejected verbatim
  with the specific excluded feature(s) and, for semantic hits, the taint path.
- `PASS { register_version }` — no exclusion fired; the submission proceeds to
  Solidus import + adjudication (§3).

**How it composes with the importer's fail-closed guard.** Solidus's importer
**already** fails closed (`guard_no_unsupported_nodes`, line 416): it partitions
every node/field/scalar into `supported | metadata | excluded | unimplemented |
unclassified` and `fail()`s on anything not `supported`/`metadata`. The gate's job
is to **classify that failure's cause**:

1. Gate runs first. If it returns `OUT_OF_SCOPE`, adjudication stops — rejected as
   intentional-exclusion. The importer is never invoked.
2. If the gate returns `PASS`, run the importer.
   - Importer `fail()` with reason class `excluded` (an `EXCLUDED_NODE_TYPES` hit)
     ⇒ **contradiction** — the gate should have caught it. This can only happen if
     the register and `EXCLUDED_NODE_TYPES` drifted; treated as a gate bug, not a
     coverage gap. (The shared-table design of §1.1 makes this unreachable.)
   - Importer `fail()` with reason class `unimplemented` / `unclassified child
     field` / `unclassified scalar` / `unknown scalar value` ⇒ this is a **genuine
     COVERAGE gap** (lane C): an in-scope feature the importer cannot yet
     translate. The specific `fail()` message (node type / field / scalar) is the
     gap identity.
   - Importer succeeds ⇒ proceed to type-check/elaborate/execute; a fail-closed
     rejection *there* (TypeCheck sentinel, elaboration `none`) is also a lane-C
     coverage gap **if** solc accepted+ran the program.

So the pipeline turns Solidus's existing fail-closed partition into the contest's
classifier: `excluded` ⇒ OUT_OF_SCOPE, every other fail-closed reason ⇒ candidate
COVERAGE_GAP, execution-with-different-observable ⇒ candidate SOUNDNESS_GAP.

---

## 3. Multi-contract execution — decision

### Decision: **Option A — closed-world execution of all submitted contracts,
implemented as a reflective responder over the existing open-world seam.**

Submissions may deploy multiple contracts that call each other. We run **all**
submitted contracts under Solidus and resolve each external call to the actual
submitted callee, executed through the interpreter. Crucially, this does **not**
require abandoning the open-world architecture — it is expressible as a
**reflective answerer** plugged into the exact seam scripted responders already
occupy.

### 3.1 Why Option B (keep open-world, abstract the external world) is inadequate

Under Option B the callee is abstracted: its return value/postWorld are supplied
by the entrant (a scripted responder) rather than computed. Two fatal problems for
a *value-divergence* contest:

1. **You cannot validate a specific multi-contract interaction's value.** The
   whole point of a soundness submission is "contract A calls contract B and the
   composed result differs." If B is abstracted, the composed value is whatever
   the entrant scripted — there is nothing to check against solc+EVM. The
   divergence, if any, lives entirely inside B, which Solidus never ran.
2. **The adversary's external contract can weaponize excluded features.** If the
   entrant supplies B's behavior (or B is a real contract answered abstractly),
   B's body can read `gasleft()`/`msize`/create2 addresses to *manufacture* a
   difference that is really an artifact of an intentional exclusion — precisely
   the SEM-GAS / SEM-ADDR / SEM-CODE hazards. Abstraction hides B from the reject
   gate's whole-submission scan, defeating §2.

The exclusion-gate-scans-every-contract rule (§2) plus closed-world reflective
execution resolves the maintainer's stated worry ("run all contracts with our
semantics? or abstract the external world but then deal with their contracts using
gas() to distinguish"): we run **all** contracts with Solidus (so composed values
are real and checkable), and the gate has already scanned **all** of them (so no
callee can smuggle `gasleft()`).

### 3.2 Feasibility of the reflective responder — MODEST, argued from the code

The existing architecture makes this a small, well-bounded build, because the
answerer is already a first-class, swappable function and the callee-execution
primitive already exists and already returns the exact shape needed.

**The seam already exists.** `SolI.runFailOpen` (Interpreter.lean:2750) folds a
tree against **any** `responder.answer : (q : Query) → Answer q`
(`ScriptedResponder.answer`, :2729). Today that function answers `Query.external`
from static oracle rows (`answerCall?`/`answerCreate?`, :2601/:2641). A reflective
answerer is a drop-in replacement at this exact seam — no interpreter change to
the fold's callers.

**The callee-execution primitive already exists and already returns the right
shape.** `Contract.callCalldataAtFromWithContext?` (ABI.lean:676) takes
`(fuel, contract, base : Context, state : State, self sender value : Word,
calldata : Bytes)` and returns `AbiCallResult { success, output, state }` — success
flag, ABI-encoded return/revert bytes, and the post-execution `State`. That is
**exactly** what a `CallResponse { success, returnData, postWorld, returnedGas }`
needs.

**The world plumbing already exists and is proved.** Each `Query.external` carries
the caller's real `snapshotWorld context state` (Interpreter.lean:2102). The
reflective answerer, to run callee B:

1. Decode the `CallRequest`: `codeAddress` → look up B in a **contract registry**
   (the new piece: a `Word → Contract` map built once from the submitted+compiled
   sources, keyed by deploy address); `caller`, `transferValue`, `calldata`.
2. Build B's entry `Context`/`State` from the carried `world` (the caller's
   snapshot) — reusing the same `adoptWorld`-style seed that already turns a world
   into interpreter state (`snapshotWorldSeed`, :2074; `adoptWorld`, :2133).
3. Run `Contract.callCalldataAtFromWithContext? fuel B … calldata`.
4. Encode the result back: `AbiCallResult.output → returnData`, `.success`, and
   `snapshotWorld` of B's post-`state` → `CallResponse.postWorld`. On resume the
   caller `adoptWorld`s it — and the proved round-trip law
   `snapshotWorld (adoptWorld w …) = w` (`AdoptionLaws.lean`) guarantees the
   caller sees exactly B's post-world, i.e. closed-world composition is sound by
   the *same* law that makes reentrancy adoption sound.

Creates are symmetric via `answerCreate?`/`decodeCreationInitCode?`: the reflective
create decodes `name‖args`, finds the contract by name in the registry, runs its
constructor through the interpreter, allocates a deploy address (nonce-derived —
the ordinary, non-salted `CREATE` address is in scope; salted create2 *address
prediction* stays OOS per SEM-ADDR), and returns a `CreateResponse` with the new
account's snapshot.

**The one real cost: recursion needs a fuel/depth bound.** The scripted folds
(`runWith`/`runFailOpen`) are *structural* and fuel-free because a static row
answer never re-enters the interpreter. A reflective answerer **does** re-enter
(answering A's call runs B, whose body may call C, answered by the same
answerer) — so the answerer↔interpreter loop is no longer structurally
decreasing and needs an explicit **call-depth budget** (a `Nat` that decreases per
nested external call; exhaustion ⇒ a well-defined failure, matching EVM's 1024
call-depth limit closely enough for the contest). This is the single genuinely new
recursion obligation; everything else is wiring existing pieces. Estimated build:
a `reflectiveResponder (registry) (depth)` answerer (~1 new def mirroring
`answerCall?`/`answerCreate?` but calling the interpreter instead of reading rows),
a registry builder, and a depth-bounded fold variant of `runFailOpen`. Bounded and
low-risk; it reuses `Contract.callCalldata*`, `snapshotWorld`/`adoptWorld`, and the
proved adoption law verbatim.

### 3.3 v1 fallback

If the reflective driver is not ready at launch, **v1 ships single-contract-only**
(§8): the entry contract may read env facts, but **any external call is disallowed
by the gate**. The v1 responder-free path answers every external call with a fixed
default (the call fails / returns empty) rather than executing a callee or a real
EVM interaction, so an external call — low-level `.call`/precompile, a high-level
call to another contract, `this.f()`, a `new C()` create, or a `try` — would
diverge for a NON-semantic reason. Two guards enforce this: `X-EXTCALL` (any
external call, incl. precompiles, is OOS until the v2 responder lands) and the
`V1-MULTI` guard (reject >1 independently-deployable `ContractDefinition`). This
is honest and still covers the entire G-register (G1–G22 are all single-contract,
external-call-free) and every coverage gap that is not intrinsically
multi-contract. The multi-contract + real-external-call driver is the headline v2
feature; retire both guards then.

### 3.4 Definition of "observable" and equality

The observable of a submission is the tuple the harness compares, in this order:

1. **Outcome**: `success` vs `revert` vs `panic`.
2. **Return data** (on success): ABI bytes of the entry call's return, compared
   byte-for-byte after ABI decode to the declared return types.
3. **Revert/panic data** (on failure): the 4-byte selector + ABI payload —
   `Error(string)`, `Panic(uint256)` code, or a custom error's selector+args;
   compared byte-for-byte. (An *empty* revert equals an empty revert.)
4. **Events**: ordered list of `(topics, data)` emitted by the entry call and its
   closed-world subcalls.
5. **State**: for a declared set of storage reads (the Forge test's post-call
   `assertEq`s), the final values.

Equality is **exact** on 1–4. State (5) is checked only at the storage
slots/getters the Forge test observes, because Solidus models storage layout
(spec-owned) but not memory layout. Gas is **never** part of the observable
(that is the whole of the SEM-GAS/SEM-CLOSEDGAS exclusion). The reflective
responder (Option A) is what makes 2–5 *computable* for a multi-contract
interaction; without it, subcall effects on state/events would be entrant-scripted
and unverifiable.

---

## 4. Adjudication — the two-lane decision tree

For each submission, in order (halt at the first terminal verdict):

```
0. STRUCTURE CHECK
   - Submission has: source(s) with ≥1 contract, a Forge test, a declared lane
     (C or S) and declared expected divergence (§5). Missing ⇒ REJECT_MALFORMED.

1. REAL-BEHAVIOR CHECK  (the claimed behavior must be real)
   - Compile all sources with pinned solc 0.8.35. solc error ⇒ (see 4a).
   - Run the Forge test against Foundry-EVM (pinned).
     Forge FAIL ⇒ INVALID  ("claimed behavior does not reproduce on solc+EVM").
     Forge PASS ⇒ continue.        [reuses run_forge_interpreter_harness.run_forge]

   1a. solc REJECTS the program (compile error), and the submission's lane is S
       with claim "Solidus wrongly ACCEPTS":
       - This is a valid soundness sub-case (over-accept). Record solc's error
         id (e.g. TypeError 5887). Skip Forge-run (nothing to run). Go to 3
         with mode = OVER_ACCEPT.

2. REJECT GATE  (§2)
   - Run reject_gate.py over the solc AST of ALL sources.
     OUT_OF_SCOPE ⇒ REJECTED_OOS (print the exclusion id + reason + taint path).
     PASS ⇒ continue.

3. RUN SOLIDUS
   - Import (solc_ast_to_lean_source.py) → type-check → elaborate → execute the
     entry call, under the reflective responder (§3) with the submitted registry.

   Classify:

   (a) Solidus FAILS CLOSED  (importer fail() / typecheck sentinel / elaboration
       none / execution cannot proceed), AND solc accepted+ran (step 1 Forge PASS):
         - Cause is `excluded`  ⇒ REJECTED_OOS  (register/importer drift bug; §2).
         - Cause is unimplemented / unclassified / unknown-scalar / typecheck-reject
           / elaboration-none ⇒  **COVERAGE_GAP (lane C).**   [terminal, scored]

   (b) mode = OVER_ACCEPT (step 1a): Solidus imports+typechecks+runs a program
       solc REJECTED  ⇒  **SOUNDNESS_GAP (lane S, over-accept).**  [terminal]

   (c) Solidus RUNS to completion:
         - Compute Solidus observable (§3.4). Compute solc+EVM observable from the
           Forge run.
         - Observables EQUAL      ⇒ NO_DIVERGENCE  (agree; rejected, not a gap).
         - Observables DIFFER     ⇒ **SOUNDNESS_GAP (lane S, wrong-observable).**
           Sub-kind by which component differs: wrong-value / wrong-revert /
           wrong-panic / revert-vs-success / wrong-state / wrong-events.  [terminal]

   (d) Solidus wrongly REJECTS a program solc accepts+ran (a fail-closed in 3a
       that is a *type-level over-reject*, not a missing feature): this is the
       completeness edge (G13–G16). Adjudicated as COVERAGE_GAP (lane C) with
       sub-kind OVER_REJECT — Solidus fails closed on an in-scope, solc-accepted
       program. Distinguished from a true missing-feature coverage gap only for
       scoring/dedup (§6); both are lane C.
```

Terminal verdicts that qualify for the leaderboard: **COVERAGE_GAP** (lane C) and
**SOUNDNESS_GAP** (lane S). Everything else (INVALID, REJECTED_OOS,
NO_DIVERGENCE, REJECT_MALFORMED) does not qualify and returns the specific reason.

**Precise "observable" and how equality is checked** — see §3.4. The equality
check *requires* the closed-world reflective execution of §3 whenever the entry
call reaches another submitted contract; single-contract submissions need only the
existing single-`Contract` interpreter path.

---

## 5. Submission format & harness

### 5.1 A submission contains

```
submission/
  src/*.sol              one or more flattened sources (NO import directives),
                         all contracts the interaction needs
  test/Divergence.t.sol  a Forge test that:
                           - deploys the contract(s)
                           - performs the entry interaction
                           - asserts the REAL solc+EVM observable (must PASS)
  claim.json             { lane: "C"|"S",
                           entry: { contract, function, args, value },
                           expected_divergence: "<free text + structured>",
                           declared_observable: { kind, solc_value },
                           register_version_seen }
```

`claim.json` makes the submission self-describing: which lane, what the entrant
believes Solidus does wrong, and the solc value they measured. The harness does
not trust `declared_observable` — it recomputes both sides — but uses it to
detect misreports and to route scoring.

### 5.2 The automated pipeline (reuses the existing harness)

The adjudicator is a thin driver over `run_forge_interpreter_harness.py`'s proven
Forge-vs-Solidus machinery:

1. **Forge** — `run_forge(case)` (existing) compiles with pinned solc and runs the
   Foundry test; must PASS (step 1). For OVER_ACCEPT claims, capture solc's reject
   instead (step 1a) via the existing `run_solc_rejects` path.
2. **Reject gate** — new `reject_gate.py` over the solc AST (step 2). solc AST is
   already produced by `solc_ast_to_lean_source.py`'s `--ast-compact-json` call;
   the gate reuses that JSON.
3. **Import + Lean** — `run_solc_import` + `run_lean` (existing) build the Lean
   file (`import …; set_option maxHeartbeats …; <generated source>; #eval …`) and
   execute the entry call. The `#eval` uses the same `Contract.call*` /
   `checkedOwnCall*Matches` entrypoints the corpus lanes use, **extended** to run
   under the **reflective responder** with the submission's contract registry
   (the multi-contract extension — the only new harness capability beyond a rename
   of inputs). Single-contract submissions use the existing responder-free path.
4. **Compare** — the driver compares the Solidus `#eval` observable against the
   Forge-measured solc+EVM observable per §3.4 and emits the §4 verdict.

The multi-contract extension needed, concretely: (i) the registry builder (map
each submitted contract to a deploy address, from the Forge test's deploy order),
(ii) the reflective-responder `#eval` harness entrypoint (§3.2), and (iii) the
observable extractor that reads events/state from the closed-world run, not just
the top return value. Nothing in the Forge/solc/import/lean *plumbing* changes.

---

## 6. Anti-gaming, dedup, scoring

### 6.1 Anti-gaming

- **(a) Excluded-feature smuggling** — defeated by §2's whole-submission scan:
  every contract (entry, callees, libraries, bases) is scanned, and the reflective
  execution (§3) means a callee cannot be an unscanned black box. Semantic
  exclusions (§1.2) use conservative taint that errs to OOS. A `gasleft()` buried
  in a transitive callee is caught before Solidus runs.
- **(b) Duplicate / known-gap resubmission** — every submission is deduped against
  **two** registries: (i) the **exclusion register** (§1) — an OOS hit is not a
  gap; and (ii) the **known-open-gaps list** — the G/H/S findings
  (`docs/solidus-solc-deep-comparison.md` G1–G22, plus any W/H items). A submission
  whose root cause matches an already-recorded open gap is **DUPLICATE** (no
  leaderboard credit to a second finder of G1). Dedup is by *root cause*, not by source text
  (§6.2). The known-gaps list is versioned alongside the register.
- **(c) Doesn't run on real solc/EVM** — step 1 (Forge must PASS on pinned
  solc+Foundry) rejects any submission whose claimed behavior is fabricated.
- **(d) Trivial variants of one root cause** — clustered in dedup: two submissions
  that both bottom out in "user-defined operator runs as builtin" (G1) collapse to
  one, first-timestamp wins. Root cause is identified by the divergence's
  *mechanism* (the failing importer message, the differing observable component,
  and the minimal feature triggering it), reviewed by the maintainer with the
  automated cluster hint.

### 6.2 Dedup mechanics

Each terminal gap gets a **fingerprint**:
- lane C: `(fail_stage, fail_reason_class, minimal_node_type_or_field)` — e.g.
  `(import, unimplemented, "SomeNode")` or `(typecheck, over_reject, "nested-tuple-LHS")`.
- lane S: `(observable_component, minimal_feature, solc_vs_solidus_delta_shape)` —
  e.g. `(return_value, "using-operator-nonbuiltin-body", …)`.
Two submissions with the same fingerprint are duplicates. The fingerprint is
compared against the known-open-gaps list (pre-registered G1–G22 fingerprints) and
against already-accepted submissions.

### 6.3 Minimality / repro requirements

- **Minimality**: the submission must reduce to the smallest program exhibiting
  the divergence — one entry function, minimal callees, no dead code. The
  adjudicator runs a **shrink check**: a submission that still diverges after
  mechanically deleting any top-level function/contract is asked to shrink (or is
  scored at reduced weight). This discourages haystack submissions hiding a known
  gap.
- **Repro**: deterministic — no `block.timestamp`/`prevrandao`-dependent
  observables unless the Forge test pins them via `vm.warp`/`vm.roll`/`vm.prevrandao`
  and the pinned env is declared in `claim.json`. The harness runs with a fixed
  block environment; any env the divergence depends on must be pinned by the test.

### 6.4 Scoring (per lane)

| | COVERAGE_GAP (lane C) | SOUNDNESS_GAP (lane S) |
|---|---|---|
| **Base** | medium | high — a wrong observable on a program both run is the worst failure class |
| **wrong-value / wrong-panic** | — | highest within S |
| **over-accept (runs solc-rejected program)** | — | high, but weighted below wrong-value (unreachable on a solc-validated corpus, per the G2–G12 analysis) |
| **over-reject (fails closed on solc-accepted program)** | scored as C sub-kind, below missing-feature | — |
| **missing feature (import/typecheck can't handle)** | full C weight | — |
| **Multipliers** | ×minimality, ×novelty (not near a known gap), ÷cluster-size (dedup) | same |

Rationale: the contest's *purpose* is to find soundness holes in an unproven
semantics, so lane S outranks lane C; within S, silent wrong-value/​wrong-panic
(a program that runs and lies) outranks over-accept/over-reject (which are
acceptance-boundary issues unreachable on a solc-validated corpus, as the G-audit
established).

---

## 7. Register/known-gaps versioning keeps the contest fair

- The **exclusion register** and the **known-open-gaps list** are both versioned
  and committed. Each submission records `register_version_seen` and is
  adjudicated against the register in force at its timestamp.
- When a gap is **fixed** (a Lean fix lands, a paired corpus lane pins it): the
  gap moves from known-open-gaps to a **known-fixed** list, and if it corresponded
  to an exclusion being retired, that register row's `removed_in_version` is set.
  Future submissions of that behavior become... valid *only* if they now genuinely
  diverge again (regression) — otherwise NO_DIVERGENCE. This is exactly the repo's
  own discipline: new corpus lanes are added only to pin a *discovered* bug
  (`ROADMAP.md:452`).
- Because syntactic detectors **import `EXCLUDED_NODE_TYPES` from the importer**,
  fixing an exclusion (e.g. enabling multi-file) is a single-source change that
  the gate picks up automatically — no drift.
- Contest fairness invariant: a submission is judged only against features that
  were *declared out of scope at submission time*. Shrinking the register later
  never retroactively invalidates an already-credited gap; it only affects future submissions.

---

## 8. Phasing — what must be built, v1 vs later

### Must exist before ANY launch (v1 core)

1. **`contest/exclusion_register.py`** — the versioned register (§1), syntactic
   detectors importing `EXCLUDED_NODE_TYPES`, semantic-detector stubs.
2. **`contest/reject_gate.py`** — the AST scan (§2): syntactic detectors (exact),
   semantic detectors with conservative taint (§1.2). Whole-submission scan.
3. **Adjudicator driver** — wraps `run_forge_interpreter_harness.py` per §4/§5:
   Forge-must-pass, gate, import, lean, observable-compare, verdict emission.
4. **Observable extractor** — §3.4 comparison for outcome/return/revert/panic/
   events/observed-state, exact equality, gas excluded.
5. **Known-open-gaps list** — pre-loaded with G1–G22 fingerprints so day-one
   submissions of the already-known gaps dedup correctly.
6. **`V1-MULTI` guard** — temporary single-contract restriction (§3.3).

**v1 ships single-contract-only.** It fully supports lane S (all of G1–G22 are
single-contract) and lane C (missing-feature + over-reject), using the existing
responder-free interpreter path. This is a legitimate, launchable contest.

### Built for v2 (the headline multi-contract capability)

7. **Reflective responder** (§3.2) — `reflectiveResponder registry depth` answerer
   mirroring `answerCall?`/`answerCreate?` but invoking
   `Contract.callCalldataAtFromWithContext?` / the constructor path; encodes
   `AbiCallResult` + `snapshotWorld` back into `CallResponse`/`CreateResponse`.
8. **Depth-bounded fold** — a fuel/call-depth variant of `SolI.runFailOpen`
   (the one genuine new recursion obligation, §3.2), with a well-defined
   depth-exhaustion failure.
9. **Contract registry builder** — deploy-address → `Contract` map from the Forge
   deploy order.
10. **Multi-contract observable extractor** — events/state across the closed-world
    subcall tree.
11. **Retire `V1-MULTI`**; enable multi-contract submissions.

### Ongoing (both phases)

- Register/known-gaps versioning discipline (§7) as fixes land concurrently on
  this branch.
- Periodic re-audit: when a G-item is fixed, move it to known-fixed and, if it was
  an exclusion, set `removed_in_version`.

### Open questions / risks

- **Reflective-responder recursion measure.** The depth-bounded fold must
  terminate; the call-depth `Nat` is the measure. Risk: choosing a bound that is
  neither too shallow (rejects legitimate deep interactions) nor unbounded. Mirror
  EVM's 1024 and make exhaustion a declared, comparable failure (solc+EVM also
  revert at depth 1024, so this is itself a checkable observable).
- **Create-address allocation parity.** Non-salted `CREATE` addresses are
  `keccak(rlp(sender, nonce))[12:]`; the registry/reflective-create must allocate
  the same address solc+EVM/Foundry uses, or address-valued observables diverge
  for a non-gap reason. Pin the nonce model to Foundry's; keep create2 *address*
  OOS (SEM-ADDR) until real initcode exists.
- **Taint-check precision (§1.2).** Conservative taint may over-reject a few
  legitimate submissions that merely *mention* `creationCode` without observing
  it. Accept the bias (resubmit-without-the-mention is cheap); log false-OOS rate
  and tighten only if it hurts participation.
- **State-observable scope.** Solidus models storage but not memory; the contest
  restricts state-observables to storage reads the Forge test performs. A
  submission whose divergence is memory-layout-only is OOS (no faithful observable)
  — fold into the register if it recurs.

---

## 9. Summary of decisions

1. **Two lanes**, adjudicated by the §4 tree: COVERAGE_GAP (Solidus fails closed
   on an in-scope, solc-accepted feature) and SOUNDNESS_GAP (Solidus runs but the
   observable differs, incl. over-accept/over-reject).
2. **Reject gate** = a whole-submission AST scan (`reject_gate.py`) over solc's AST
   of every source, run before Solidus import, reusing the importer's
   `EXCLUDED_NODE_TYPES` so the register and importer cannot drift; it **classifies**
   Solidus's existing fail-closed partition into OUT_OF_SCOPE vs coverage-gap.
3. **Exclusion register** = versioned, syntactic (exact AST predicates: assembly,
   imports, `gasleft`, `msize`, storage-layout, executable fixed-point) + semantic
   (conservative taint: gas-as-observable, `creationCode`/`runtimeCode` bytecode
   observables, create2 predicted address, closed-world gas).
4. **Multi-contract** = **Option A, closed-world reflective responder** — a modest
   build that reuses `Contract.callCalldataAtFromWithContext?`,
   `snapshotWorld`/`adoptWorld`, and the proved adoption round-trip law, plugged
   into the existing `ScriptedResponder.answer`/`runFailOpen` seam; the only new
   recursion obligation is a call-depth-bounded fold. Option B is inadequate
   because abstracted callees make composed values unverifiable and let callees
   smuggle excluded features.
5. **Phasing** = v1 single-contract (covers all of G1–G22 and coverage gaps,
   responder-free) ships first; the reflective driver is the v2 headline.
```

---

## Changelog

### 2026-07-08 — v1.2: leaderboard reframing, RCE/oracle-forgery fixes, events+storage observable

Reframed as a **for-fun leaderboard** (no monetary component; `Report.pays_out` →
`Report.qualifies`). A second adversarial pass (harness-level) found defects the
v1.1 pass did not close; all are now fixed in `contest/*.py` and validated by
`contest/run_samples.py`.

**Security — untrusted execution (see `docs/contest-security-and-sandbox.md`).**
- **Cheatcode detection re-centred on the cheatcode ADDRESS**, over BOTH `src/`
  and `test/`, *before* any Forge run (`reject_gate.scan_cheatcodes`). Catches
  the two bypasses the identifier-name detector missed — an aliased handle
  (`CVm c = CVm(HEVM_ADDRESS); c.ffi()`) and a raw
  `address(0x7109…).call(...)` — and closes the `src/`-forges-the-oracle hole
  (the measurement deploys and calls the entry contract, so a cheatcode call
  from `src` could rewrite the measured EVM observable).
- **Forge never runs the submitter's `foundry.toml`.** Both the real-behavior
  check and the measurement generate a pinned profile with `ffi = false` and a
  minimal `fs_permissions`; the measurement output now lives OUTSIDE the project
  tree so the deployed contract cannot write it.
- **Untrusted claim fields validated before codegen**: `entry.contract` /
  `entry.function` must be identifiers in ALL paths (blocks Lean string
  injection, incl. OVER_ACCEPT); `fuel ∈ [1, 100000]`; `entry.args` /
  `observed_slots` shape/range-checked → `REJECT_MALFORMED`, not a crash.
- **Inconclusive Solidus failures** (timeout / resource exhaustion / poisoned
  `fuel`) → new non-qualifying **`NEEDS_REVIEW`** verdict, never an automatic
  `COVERAGE_GAP`.
- **V1-MULTI** no longer counts base contracts in the entry's inheritance chain
  (ordinary inheritance from a concrete base was wrongly rejected);
  **X-STORAGELAYOUT** matches the node type precisely.

**Observable — components 4 (events) and 5 (storage) are now COMPARED (§3.4).**
The Lean helper (`observable.renderFull` / `renderEvents` / `renderStorageAll`)
extracts events and the WHOLE post-call storage map from the post-call `State`
and renders them in a tokenized normal form (`…##EVT##…##STO##…`); the EVM side
measures the same via `vm.recordLogs`/`getRecordedLogs` for events and
`vm.record`/`vm.accesses` + `vm.load` for the full storage map (`measure.py`).
The comparator diffs component-by-component, adding sub-kinds `wrong-events` and
`wrong-state`; storage is normalized to an order-independent `{slot: value}` map
(zeros dropped) before diffing. Events/storage are compared only on success (the
EVM rolls both back on revert). **Storage divergence is auto-detected across all
slots** — no `claim.observed_slots` declaration is needed (the field is accepted
but ignored), and mappings/dynamic arrays are covered via their keccak-derived
slots. The entry call runs against the **post-construction** state: Solidus runs
the constructor + initializers (`constructWithContext`) before the entry call,
mirroring the EVM `new C()`, so initialized storage is not a false divergence.
Validated end-to-end against the built Solidus (`ctor_storage` sample +
`run_real_storage_selftest`).

**Gap-testing without leaving bugs in Solidus.** The soundness detector is now
tested by a REAL end-to-end run (`run_real_soundness_selftest`): the full live
pipeline executes a real contract, then a **one-unit delta is injected at the
observable boundary** (`observable.perturb_leading_value`, via the
`_selftest_perturb_evm` seam) so the divergence-detection path is exercised over
a genuine Solidus execution while Solidus stays bug-free. When a real coverage
gap is available it is pinned as a fixture whose expected verdict flips to
NO_DIVERGENCE once fixed — a bug is never kept alive to test detection.

### 2026-07-08 — v1.1 hardening (`contest/v1.1-hardening`): the three CONTEST-BREAKING defects closed

The adversarial review (`docs/competition-design-review.md`, commit `368468a`) found
three plan-level defects that let an adversary bank a fake `SOUNDNESS_GAP` (or
mis-lane an honest submission). All three P0 fixes plus the two P1 items are now
implemented and validated by attack samples in `contest/samples/`.

**P0 #1 — the EVM observable is MEASURED from the Forge run, not the submitter's
declared string.** `adjudicate.py` no longer feeds `claim.declared_observable`
to the comparator. Instead `contest/measure.py` generates a Foundry harness that
deploys the entry contract, performs the ENTRY call by raw calldata under the
pinned env, and dumps the raw `(ok, ret-bytes, self, origin)`; `observable.py`
(`evm_observable`) decodes those bytes into the normal form and the comparator
diffs Solidus's `#eval` against THAT. `declared_observable` is kept only as a
misreport cross-check (`evidence.declared_mismatch`). Attack: `fake_oracle/`
(trivially-passing test, `declared_observable = success|w:999`, `run()` really
returns 5) — **before:** SOUNDNESS_GAP(wrong-value); **after:** NO_DIVERGENCE.

**P0 #2 — one canonical environment, pinned identically on both engines.** The
canonical env is Foundry's REAL defaults, measured (not guessed) with forge
1.5.1 + solc 0.8.35, evm_version=cancun: `block.number=1`, `block.timestamp=1`,
`block.chainid=31337`, `block.basefee=0`, `block.coinbase=0`,
`block.prevrandao=0`, `block.gaslimit=1073741824`, default caller/`tx.origin`
`0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38`; `address(this)` is the deployed
entry-contract address, measured from the run and mirrored. `contest/env.py`
holds these; the Solidus `#eval` threads them into the Context/BlockEnv via the
pre-existing public `CheckedContract.callFunctionWithContext` entry point (no
change to SolidCore), and `contest/measure.py` re-pins the identical values on
the Foundry side. A new env-fact detector (`SEM-ENV`, register bumped to
`1.1.0`) classifies an observable derived from an UNPINNABLE env fact
(`blockhash`/`blobhash`) as `OUT_OF_SCOPE` rather than a spurious divergence.
Attacks: `env_divergence/` (`return block.timestamp`) — **before:**
SOUNDNESS_GAP(wrong-value 1-vs-0); **after:** NO_DIVERGENCE. `env_blockhash/`
(`return blockhash(0)`) — **after:** REJECTED_OOS (SEM-ENV).

**P0 #3 — cheatcodes restricted; the TEST file is scanned.** `reject_gate.py`
now scans the submission's TEST ASTs (compiled together with `src/` so imports
resolve, `multi_source_asts`). Policy (`contest/env.py`, DEFAULT-DENY):
allowed/mirrored env-pinning cheatcodes are `vm.roll` (number), `vm.warp`
(timestamp), `vm.chainId`, `vm.fee` (basefee), `vm.prevrandao`,
`vm.prank`/`vm.startPrank`(+`stopPrank`) (msg.sender), `vm.deal` (balance) —
their literal effect is mirrored into the Solidus env; everything else on
`vm.*`/`hevm.*` is rejected (`vm.store`, `vm.load`, `vm.mockCall(Revert)`,
`vm.ffi`, `vm.etch`, `vm.expectRevert`/`vm.expectEmit`, `vm.record`,
`vm.readFile`/`writeFile`, ...); a whitelisted cheatcode with a non-literal
argument that cannot be mirrored is also rejected. `console.*` logging is an
ignored no-op. Attacks: `cheatcode_banned/` (`vm.store` to forge storage) —
**after:** REJECTED_OOS; `cheatcode_allowed/` (`vm.warp(12345)`) — **after:**
allowed, mirrored, NO_DIVERGENCE (both engines see `timestamp=12345`).

**P1 — `run_solc_rejects` by exit code + error code.** `harness_bridge.py`
`run_solc_rejects_source` now requires a non-zero solc exit AND a real
error-level diagnostic (warnings, exit 0, never count); an optional
`claim.solc_error_code` pins the reject to a specific solc error code.

**P1 — env-observable register entry** = `SEM-ENV` (above).

**Validation.** `contest/run_samples.py` runs the full suite against pinned solc
+ Foundry + the built Solidus in this worktree: the original four stay green
(`oos_gasleft`→REJECTED_OOS, `no_divergence`→NO_DIVERGENCE, plus the two
synthetic Solidus-simulated `coverage_gap`→COVERAGE_GAP /
`soundness_gap`→SOUNDNESS_GAP — the latter now diffs against the REAL measured
EVM observable), and all five new attack/allowed samples classify correctly.

**Scope note.** This hardens the SINGLE-CONTRACT restricted launch. The Lean
env-threading required no SolidCore change (the `...WithContext` call family
already accepts a `Context`). Documented v1 precision limits: custom-error revert
comparison (EVM side decodes to `raw:`, routed to review), and the coarse
function-level taint (review G-2) are unchanged and remain human-sign-off items.
