# Divergence Contest — v1 reject-gate + adjudication harness

> **Testing your own divergence submission?** See **[SUBMITTING.md](SUBMITTING.md)**
> for prerequisites (build the Lean model, pinned solc 0.8.35, Foundry), the
> submission layout + `claim.json` schema, and how to run
> `python -m contest.adjudicate`.

Implements `docs/competition-design.md` for the **single-contract** (v1) scope:
the reject gate, exclusion register, adjudicator decision tree, observable
extractor/comparator, and dedup fingerprints, wired end-to-end against pinned
solc 0.8.35 + Foundry + the built solidity-lean (Lean) in this worktree.

The multi-contract reflective responder (design §3, v2) is **out of scope for
v1**; the seam where it plugs in is documented in `multi_contract.py` and the
temporary `V1-MULTI` gate guard rejects multi-contract submissions until then.

## v1.1 hardening (2026-07-08) — the oracle is now trustworthy

The adversarial review (`docs/competition-design-review.md`) found three
CONTEST-BREAKING defects; all three P0 fixes + two P1 items are implemented
(see the design doc's **Changelog** for the full write-up and before→after
verdicts). In short:

- **Measured, not declared (P0 #1).** The EVM observable is measured from an
  actual Forge run (`measure.py`) and decoded (`observable.evm_observable`);
  `claim.declared_observable` is only a misreport cross-check.
- **Pinned environment (P0 #2).** ONE canonical env = Foundry's real defaults
  (`env.py`), threaded identically into the solidity-lean `#eval`
  (`CheckedContract.callFunctionWithContext`) and the Foundry measurement. An
  env-fact detector (`SEM-ENV`) rejects `blockhash`/`blobhash`-derived
  observables as out of scope.
- **Cheatcode allow-list (P0 #3).** The TEST AST is scanned. DEFAULT-DENY.

### Cheatcode policy (allow-list; everything else rejected)

| Allowed (mirrored into the solidity-lean env) | Effect |
|---|---|
| `vm.roll(n)` | `block.number` |
| `vm.warp(t)` | `block.timestamp` |
| `vm.chainId(id)` | `block.chainid` |
| `vm.fee(f)` | `block.basefee` |
| `vm.prevrandao(x)` | `block.prevrandao` |
| `vm.prank`/`vm.startPrank(a)` (+`stopPrank`) | `msg.sender` |
| `vm.deal(a, amt)` | balance |

Whitelisted cheatcodes must use **literal** arguments (so the value can be
mirrored). `console.*` logging is an ignored no-op. **Banned** (submission
rejected): `vm.store`, `vm.load`, `vm.mockCall`/`mockCallRevert`, `vm.ffi`,
`vm.etch`, `vm.expectRevert`/`expectEmit`, `vm.record`, `vm.readFile`/`writeFile`,
`vm.setNonce`, and anything else on `vm.*`/`hevm.*` (default-deny).

### Canonical env (Foundry's real defaults, measured — not guessed)

`block.number=1`, `block.timestamp=1`, `block.chainid=31337`, `block.basefee=0`,
`block.coinbase=0`, `block.prevrandao=0`, `block.gaslimit=1073741824`, default
caller / `tx.origin` `0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38`;
`address(this)` = the measured deploy address, mirrored so it agrees by
construction.

## Quick start

```bash
# Adjudicate one submission (full pipeline: solc + Foundry + solidity-lean):
python -m contest.adjudicate contest/samples/no_divergence

# Just the reject gate over some sources:
python -m contest.reject_gate path/to/*.sol

# Print the exclusion register / known-gaps registry:
python -m contest.exclusion_register
python -m contest.known_gaps

# Run the sample suite (proves every classification path):
python -m contest.run_samples
```

## Submission format (design §5.1)

```
submission/
  src/*.sol       flattened source(s), NO import directives; all contracts the
                  interaction needs (v1: a single concrete contract).
  test/*.t.sol    a Forge test that deploys, performs the entry interaction, and
                  asserts the REAL solc+EVM observable (must PASS on pinned
                  solc 0.8.35 + Foundry). Plain `require`-based tests work; no
                  forge-std dependency is needed (runs `--offline --no-auto-detect`).
  foundry.toml    minimal Foundry project config (src/test/evm_version).
  claim.json      the self-describing claim (below).
```

`claim.json`:

```json
{
  "lane": "C" | "S",
  "entry":   { "contract": "Name", "function": "fn", "args": [ ... ], "value": 0 },
  "expected_divergence": "free text",
  "declared_observable": { "kind": "return_value", "normal_form": "success|w:5" },
  "feature": "minimal-triggering-feature",       // used for dedup
  "register_version_seen": "1.6.0",
  "mode": "OVER_ACCEPT",                          // optional: solc-rejects sub-case
  "observed_slots": [0, 1],                       // vestigial: storage is now compared in full
  "fuel": 64                                      // optional: interpreter fuel (1..100000)
}
```

`observed_slots` is **no longer required** — storage divergence is auto-detected
across the WHOLE storage map (see component 5 below); the field is accepted for
backward compatibility but ignored. `fuel` (optional, default 64, capped at
100000) bounds the solidity-lean interpreter; out-of-range values are rejected
`REJECT_MALFORMED`.

**Entry args** (`observable.render_lean_arg`): `2` → `uint`; `{"int": -8}` →
signed `int256`; `true`/`false` → bool; `{"word": n}`; `{"bytes": "0x…"}`.
Register ≥ 1.4.0: a JSON **list** encodes an array or struct argument
(arbitrarily nested; validated recursively per element/member against the
declared parameter type, then type-directed ABI-encoded for the EVM and
rendered as the matching aggregate `Value` for the Lean side).

**`declared_observable.normal_form`** is the solc+EVM observable in the contest
**normal form** (below). It is validated real by the Forge test passing, and the
comparator checks the solidity-lean observable against it.

## The observable (design §3.4)

Compared, in order, with **exact** equality; **gas is never included**:

1. outcome — success / revert / panic
2. return data (success)
3. revert/panic data (Error(string) / Panic(code) / custom / empty / raw)
4. events — ordered `(topics, data)` emitted by the entry call (compared on
   success; the EVM rolls them back on revert)
5. observed storage — the WHOLE post-call storage map (every non-zero slot the
   constructor, initializer, or entry call wrote), compared on success. No
   declaration required; mappings/dynamic arrays are covered via their
   keccak-derived slots.

Events (4) and storage (5) are measured on both engines and compared
component-by-component (sub-kinds `wrong-events` / `wrong-state`): the solidity-lean
side extracts them from the post-call `State` (`observable.renderFull` /
`renderStorageAll`), the EVM side via `vm.recordLogs`/`getRecordedLogs` for
events and `vm.record`/`vm.accesses` + `vm.load` for the full storage map
(`measure.py`). Storage is normalized to a `{slot: value}` map (zeros dropped,
order-independent) before diffing. Both are rendered in the same tokenized
normal form (`…##EVT##…##STO##…`).

**Contract deployment:** the entry call runs against the **post-construction**
state — solidity-lean runs the (possibly synthesized) constructor and state-variable
initializers via `constructWithContext` before calling the entry function,
mirroring the EVM side's `new C()`. Contracts with initialized storage therefore
do not produce a spurious divergence. A constructor that **reverts** is a
first-class measured observable: both engines render the deploy-phase outcome
under the distinct `deployrevert|…` head (same revert bodies as `revert|…`),
so a constructor-revert divergence is compared, not excluded — and a
deploy-phase revert can never compare equal to a call-phase one.

**Normal form** (a single canonical line, independent of solidity-lean's `Repr`):

```
success|<v1>,<v2>,...        # values: w:<nat> | i:<int> | b:<hex> | [..] | (..)
revert|empty
revert|panic:<code-decimal>
revert|error:<string>
revert|custom:<name>:<v1>,...
revert|raw:<hexbytes>
deployrevert|<same bodies>   # the CONSTRUCTOR reverted (deploy-phase; never
                             # compares equal to a call-phase revert)
solidity-lean-reject|<message>     # solidity-lean fail-closed (import/typecheck/exec)
```

The solidity-lean side is computed by a Lean `#eval` of the helper
`observable.LEAN_OBSERVABLE_HELPER` (new tooling text; it only consumes public
entry points — `CheckedInput.ownCall`, `CallResult`, `RevertData`, `Value` — and
does **not** modify `SolidCore/**`).

## Components

| File | Role |
|---|---|
| `exclusion_register.py` | Versioned register (§1). Syntactic AST-level entries **reuse the importer's `EXCLUDED_NODE_TYPES`** (imported, not re-typed) so register/importer cannot drift. `REGISTER_VERSION`, `removed_in_version` for retirement. |
| `reject_gate.py` | Whole-submission AST scan (§2). Syntactic detectors (exact) + semantic taint detectors (conservative). `V1-MULTI` guard. |
| `observable.py` | Observable definition, Lean helper, normal-form parse/compare (§3.4). |
| `harness_bridge.py` | Reuses `run_forge` / `run_solc_rejects` / `run_solc_import` from `scripts/run_forge_interpreter_harness.py`; runs solidity-lean + captures the observable `#eval`. |
| `known_gaps.py` | Known-gap registry (§6.2), v2: entries carry their repro; keys are DERIVED from the repro by `fingerprint.py` (never hand-written) and invariant-tested. `KNOWN_FIXED` for retired gaps. |
| `fingerprint.py` | The ONE canonical repro fingerprinter: structural hash of the pinned-solc AST, alpha/order/comment-invariant, distinctness-preserving. |
| `adjudicate.py` | The §4 decision tree + CLI entrypoint. |
| `multi_contract.py` | **v2 seam** (stub): where the reflective responder / depth-bounded fold / registry / multi-contract observable plug in. |
| `run_samples.py` | Sample-suite runner; asserts each path classifies correctly. |

## The reject gate scans the WHOLE submission

The gate gets the pinned-solc AST of **every** `src/*.sol` (via the importer's
`run_solc_ast`, so it is byte-for-byte what solidity-lean imports) and scans **every**
`ContractDefinition` — entry, callees, libraries, bases — not just the named
entry. An adversary hiding `gasleft()` in a transitive callee is caught (see the
`oos_gasleft` sample, whose `gasleft()` lives in an `internal` callee).

* **Syntactic detectors (§1.1)** — exact predicate over `nodeType` / `memberName`
  / directive presence: X-ASM, X-IMPORT (both **sourced from the importer's
  `EXCLUDED_NODE_TYPES`**), X-GASLEFT, X-MSIZE, X-STORAGELAYOUT, X-EXTCALL.
  Two further syntactic rows are **adjudicator-checked** (they need the entry
  signature, which a whole-source gate scan does not know): X-INTFNARG
  (internal-function-typed / domain-unboundable entry+constructor parameters —
  EXTERNAL function-typed parameters are measured since 1.6.0 via the
  `[address, selector]` claim arg form) and X-INTFNVAL (internal function
  values in the return/revert channel). X-EXTCALL carries a precompile
  CARVE-OUT since 1.6.0: a plain `.staticcall` whose receiver constant-folds
  to a literal precompile address 1..10 is answered in-semantics (real
  precompile output on both engines) and is therefore in scope; every other
  call form (plain/valued `.call`, delegatecall, `{gas:..}` options, computed
  receivers) stays excluded.
* **Semantic detectors (§1.2)** — feature-presence **plus a conservative taint
  pass**: a value derived from the excluded quantity (gas, real bytecode,
  create2 address, unpinnable env facts, closed-world gas/stipend) reaching an
  **observed** position (assert / return / emit): SEM-GAS, SEM-CODE, SEM-ADDR,
  SEM-ENV, SEM-CLOSEDGAS.

### Register history (current: **1.6.0** — it SHRINKS as the harness grows)

Retired rows are kept with `removed_in_version` (never deleted), and each
submission is judged against the register in force at its timestamp:

* **1.3.0** retired **X-RETABI** and **X-ERRSEL**: the recursive ABI head/tail
  codec landed, so array/struct/**nested-dynamic** RETURN values and
  custom-error REVERT params are decoded to the same `[..]`/`(..)` normal form
  on both engines and **measured**, and a colliding revert selector is resolved
  to the model-reported error and compared byte-faithfully (exactly how the EVM
  dispatches revert data).
* **1.4.0** retired **X-ARGVAL** and **X-FNVAL**: array/struct entry and
  constructor PARAMETERS are encoded end-to-end (JSON-list claim args,
  recursively domain-validated, type-directed ABI calldata vs the matching Lean
  values — the same logical call on both engines), and an EXTERNAL function
  value compares canonically as `f:<addr>:<sel>` in the return/revert channel.
  The narrow residues live on as **X-FNARG** and **X-INTFNVAL**.
* **1.5.0** retired **X-FIXED-EXEC** as redundant: every form its detector
  fired on is rejected by solc 0.8.35 itself at codegen (so no such program can
  pass the Forge gate), and the solc-compilable fixed-point forms (bare
  declarations, `delete`, decl-init) never triggered it and are covered by the
  `fixed-point-boundary` corpus lane.
* **1.6.0** retired **X-FNARG** (external half closed; the internal-only
  residue lives on as **X-INTFNARG**) and carved precompile staticcalls out of
  **X-EXTCALL**. An EXTERNAL function-typed entry/constructor parameter is now
  encoded end-to-end: the claim arg is a 2-element `[address, selector]` list
  (address < 2^160, selector < 2^32), the EVM receives the 24-byte left-packed
  ABI word `(addr << 96) | (sel << 64)` (verified against solc 0.8.35's own
  encoder/decoder) and the model receives `Value.externalFunction` — the same
  pair both engines render as `f:<addr>:<sel>` since 1.4.0. CALLING the
  supplied value stays OOS under X-EXTCALL (no callee exists in the v1
  responder-free world). And a plain `.staticcall` whose receiver
  constant-folds to a literal precompile address **1..10** is now IN SCOPE:
  the engine answers all ten mainnet precompiles in-semantics with the real
  output (86-case parity suite vs geth+revm; sample `precompile_all10` pins
  byte-identical outputs end-to-end, including bn254 pairing and KZG point
  evaluation). Engine-probe evidence bounds the carve-out: only zero-value
  STATICCALL requests are answered, so plain/value-bearing `.call`,
  `delegatecall`, `{gas:..}`-optioned calls, and computed (non-literal)
  receivers remain excluded.
* **Constructor reverts are measured**, not excluded: a reverting constructor
  renders the `deployrevert|…` observable on both engines (see below).
* **Contract creation** (`new C()`, salted/valued creates — CREATE/CREATE2)
  remains explicitly out of scope under **X-EXTCALL** until the v2 reflective
  responder lands; in-memory `new T[](n)` / `new bytes(n)` are not creations
  and stay in scope.

### Taint precision limit (documented)

The taint pass is deliberately **conservative — it errs toward OOS**. v1
approximates “reaches an assertion/observed return” as *“the excluded quantity
appears in a function that also has an assert/return/emit”* — a coarse
whole-function reachability, not precise def-use dataflow. A false OOS costs one
entrant a resubmission with the observable removed; a false PASS would let an
adversary bank a fake divergence, so the bias is correct (design §1.2, §8).

## How the adjudicator classifies (design §4)

Two qualifying lanes (COVERAGE_GAP, SOUNDNESS_GAP); everything else is
non-qualifying. Qualifying submissions earn a place on the leaderboard. For the
untrusted-execution / sandbox requirements of a public deployment see
`docs/contest-security-and-sandbox.md`.

* **REJECT_MALFORMED** — structure check failed (missing src/test/claim/entry) or
  an invalid claim field (bad identifier, out-of-range fuel/slots, malformed args).
* **INVALID** — the claimed behavior does not reproduce on pinned solc+Foundry
  (Forge did not PASS; or an OVER_ACCEPT claim where solc did not reject).
* **REJECTED_OOS** — the reject gate fired (intentional exclusion, or a banned
  cheatcode / cheatcode-address reference in src or test).
* **NEEDS_REVIEW** — solidity-lean failed *inconclusively* (timeout / resource
  exhaustion), not a clean reject; routed to a human, never auto-qualified.
* **COVERAGE_GAP (lane C)** — solidity-lean **fails closed** (importer `unimplemented`
  / typecheck / elaboration reject; incl. **over-reject**) on an in-scope,
  solc-accepted program. *Qualifies for the leaderboard.*
* **NO_DIVERGENCE** — solidity-lean runs and its observable **equals** solc+EVM's (or
  both reject).
* **SOUNDNESS_GAP (lane S)** — solidity-lean **runs** but the observable **differs**
  (wrong-value / wrong-panic / wrong-revert / revert-vs-success), **or**
  over-accept (solidity-lean runs a program solc rejects). *Qualifies for the leaderboard.*

**EVM-side observable — MEASURED, not declared.** The solc+EVM observable is
**measured** from a harness-generated Forge run (`measure.py` deploys the entry
contract with `new C()` / a low-level `create` and calls the entry by selector,
independently of the submitter's test) and decoded to the normal form
(`observable.evm_observable`). The submitter's Forge test must PASS as a
real-behavior gate, but its assertions do NOT feed the oracle:
`claim.declared_observable` is only a **misreport cross-check** (a disagreement is
recorded in evidence; adjudication always uses the MEASURED value). The
solidity-lean side is independently recomputed by the Lean `#eval`. This is what
defeats the "trivially-passing test declaring a false observable" attack — do NOT
regress the adjudicator to read the declared value.

## Dedup (design §6.2, registry v2)

Every terminal gap still gets a **live fingerprint** on its report (used by the
fix-time replay to compare E0 vs E1 runs of the same submission):

* lane C: `(fail_stage, fail_reason_class, minimal_node_type_or_field)`
* lane S: `(observable_component, minimal_feature, delta_shape)`

The **registry keys** in `known_gaps.py`, however, are never hand-authored
(v2): every entry carries its repro (`repro_dir`, a corpus lane), and its key
is DERIVED from that repro by the one canonical fingerprinter
(`fingerprint.py` — a structural, rename/reorder/comment-invariant hash of the
pinned-solc AST). Keys are cached in `known_gap_fingerprints.json`
(`python3 -m contest.known_gaps --rebuild`) and the registry invariant test
re-derives every one, so a key can never silently de-sync from the
fingerprinter. Auto-match (`duplicate_of: <id>`) fires only on an EXACT
canonical-AST match — i.e. the submission is a published repro up to
renaming/reordering; anything else surfaces as advisory hints only
(`feature_hint`, `delta_cluster_hint`) for the maintainer + fix-time replay.
Entries whose repro is not yet recovered carry no key and are excluded from
auto-match (`python3 -m contest.known_gaps --no-repro`).

## v2 seam — multi-contract (design §3, §8)

`multi_contract.py` documents exactly where v2 plugs in over the existing,
proved open-world seam: (1) contract registry builder, (2) `reflectiveResponder
registry depth` answerer reusing `Contract.callCalldataAtFromWithContext?` +
`snapshotWorld`/`adoptWorld` + the proved adoption round-trip law, (3) the
depth-bounded fold (`DEFAULT_CALL_DEPTH = 1024`), (4) multi-contract observable
extractor (events/state across the subcall tree), (5) retiring `V1-MULTI`. The
v1 single-contract path is the responder-free special case, so v2 is wiring.

## Samples (`contest/samples/`, run via `run_samples.py`)

~57 fixtures, each a complete adjudicable submission proving one classification
path end-to-end (real solc + Foundry + the built solidity-lean). Highlights:

| Family | What it proves |
|---|---|
| `no_divergence`, `oos_gasleft`, `env_divergence`, `cheatcode_*` | the happy path, the gate (incl. a `gasleft()` hidden in a callee), env pinning, the cheatcode allow/deny list |
| `panic_*`, `revert_*`, `custom_error_*`, `nested_error_revert`, `error_selector_collision` | the revert/panic channel incl. nested-dynamic custom errors and colliding selectors (X-ERRSEL retired) |
| `array_return`, `nested_dynamic_return`, `struct_return`, `*_return` | the decoded return channel (X-RETABI retired) |
| `array_arg`, `nested_array_arg`, `struct_arg`, `struct_dyn_arg` (+ `*_malformed` controls) | array/struct parameters encoded end-to-end + domain validation (X-ARGVAL retired) |
| `extfn_return`, `fn_param_oos` | external fn values compare (`f:<addr>:<sel>`, X-FNVAL retired); fn-typed params stay OOS (X-FNARG) |
| `ctor_revert_*` (five) | constructor reverts measured as `deployrevert\|…` on both engines |
| `coverage_gap` / `soundness_gap` | the classifier decision tree, with the solidity-lean step **SIMULATED** (marked `synthetic`: no live gap is kept alive in the model just to drive a test; the live paths are separately proven by perturbation self-tests) |

`run_samples.py` also unit-tests the observable comparator, the dedup
fingerprints, the registry invariant (stored fingerprint ==
fingerprinter(repro) for every known-gap entry), and runs perturbation
self-tests over genuine executions.
