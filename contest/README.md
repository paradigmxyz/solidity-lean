# Divergence Contest — v1 reject-gate + adjudication harness

Implements `docs/competition-design.md` for the **single-contract** (v1) scope:
the reject gate, exclusion register, adjudicator decision tree, observable
extractor/comparator, and dedup fingerprints, wired end-to-end against pinned
solc 0.8.35 + Foundry + the built Solidus (Lean) in this worktree.

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
  (`env.py`), threaded identically into the Solidus `#eval`
  (`CheckedContract.callFunctionWithContext`) and the Foundry measurement. An
  env-fact detector (`SEM-ENV`) rejects `blockhash`/`blobhash`-derived
  observables as out of scope.
- **Cheatcode allow-list (P0 #3).** The TEST AST is scanned. DEFAULT-DENY.

### Cheatcode policy (allow-list; everything else rejected)

| Allowed (mirrored into the Solidus env) | Effect |
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
# Adjudicate one submission (full pipeline: solc + Foundry + Solidus):
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
  "register_version_seen": "1.0.0",
  "mode": "OVER_ACCEPT",                          // optional: solc-rejects sub-case
  "observed_slots": [0, 1],                       // optional: storage slots to compare
  "fuel": 64                                      // optional: interpreter fuel (1..100000)
}
```

`observed_slots` (optional) lists the storage slots compared as observable
component 5. `fuel` (optional, default 64, capped at 100000) bounds the Solidus
interpreter; out-of-range values are rejected `REJECT_MALFORMED`.

**Entry args** (`observable.render_lean_arg`): `2` → `uint`; `{"int": -8}` →
signed `int256`; `true`/`false` → bool; `{"word": n}`; `{"bytes": "0x…"}`.

**`declared_observable.normal_form`** is the solc+EVM observable in the contest
**normal form** (below). It is validated real by the Forge test passing, and the
comparator checks the Solidus observable against it.

## The observable (design §3.4)

Compared, in order, with **exact** equality; **gas is never included**:

1. outcome — success / revert / panic
2. return data (success)
3. revert/panic data (Error(string) / Panic(code) / custom / empty / raw)
4. events — ordered `(topics, data)` emitted by the entry call (compared on
   success; the EVM rolls them back on revert)
5. observed storage — the values at the slots the submission declares in
   `claim.observed_slots` (compared on success)

Events (4) and storage (5) are now measured on both engines and compared
component-by-component (sub-kinds `wrong-events` / `wrong-state`): the Solidus
side extracts them from the post-call `State` (`observable.renderFull`), the EVM
side via `vm.recordLogs`/`getRecordedLogs` and `vm.load` (`measure.py`). Both are
rendered in the same tokenized normal form (`…##EVT##…##STO##…`).

**Normal form** (a single canonical line, independent of Solidus's `Repr`):

```
success|<v1>,<v2>,...        # values: w:<nat> | i:<int> | b:<hex> | [..] | (..)
revert|empty
revert|panic:<code-decimal>
revert|error:<string>
revert|custom:<name>:<v1>,...
revert|raw:<hexbytes>
solidus-reject|<message>     # Solidus fail-closed (import/typecheck/exec)
```

The Solidus side is computed by a Lean `#eval` of the helper
`observable.LEAN_OBSERVABLE_HELPER` (new tooling text; it only consumes public
entry points — `CheckedInput.ownCall`, `CallResult`, `RevertData`, `Value` — and
does **not** modify `SolidCore/**`).

## Components

| File | Role |
|---|---|
| `exclusion_register.py` | Versioned register (§1). Syntactic AST-level entries **reuse the importer's `EXCLUDED_NODE_TYPES`** (imported, not re-typed) so register/importer cannot drift. `REGISTER_VERSION`, `removed_in_version` for retirement. |
| `reject_gate.py` | Whole-submission AST scan (§2). Syntactic detectors (exact) + semantic taint detectors (conservative). `V1-MULTI` guard. |
| `observable.py` | Observable definition, Lean helper, normal-form parse/compare (§3.4). |
| `harness_bridge.py` | Reuses `run_forge` / `run_solc_rejects` / `run_solc_import` from `scripts/run_forge_interpreter_harness.py`; runs Solidus + captures the observable `#eval`. |
| `known_gaps.py` | Dedup fingerprints for G1–G22, H1/H2 (§6.2). Root-cause keys, not source text. `KNOWN_FIXED` for retired gaps. |
| `adjudicate.py` | The §4 decision tree + CLI entrypoint. |
| `multi_contract.py` | **v2 seam** (stub): where the reflective responder / depth-bounded fold / registry / multi-contract observable plug in. |
| `run_samples.py` | Sample-suite runner; asserts each path classifies correctly. |

## The reject gate scans the WHOLE submission

The gate gets the pinned-solc AST of **every** `src/*.sol` (via the importer's
`run_solc_ast`, so it is byte-for-byte what Solidus imports) and scans **every**
`ContractDefinition` — entry, callees, libraries, bases — not just the named
entry. An adversary hiding `gasleft()` in a transitive callee is caught (see the
`oos_gasleft` sample, whose `gasleft()` lives in an `internal` callee).

* **Syntactic detectors (§1.1)** — exact predicate over `nodeType` / `memberName`
  / directive presence: X-ASM, X-IMPORT (both **sourced from the importer's
  `EXCLUDED_NODE_TYPES`**), X-GASLEFT, X-MSIZE, X-STORAGELAYOUT, X-FIXED-EXEC.
* **Semantic detectors (§1.2)** — feature-presence **plus a conservative taint
  pass**: a value derived from the excluded quantity (gas, real bytecode,
  create2 address, closed-world gas/stipend) reaching an **observed** position
  (assert / return / emit): SEM-GAS, SEM-CODE, SEM-ADDR, SEM-CLOSEDGAS.

### Taint precision limit (documented)

The taint pass is deliberately **conservative — it errs toward OOS**. v1
approximates “reaches an assertion/observed return” as *“the excluded quantity
appears in a function that also has an assert/return/emit”* — a coarse
whole-function reachability, not precise def-use dataflow. A false OOS costs one
entrant a resubmission with the observable removed; a false PASS would let an
adversary bank a fake divergence, so the bias is correct (design §1.2, §8).

## How the adjudicator classifies (design §4)

Two qualifying lanes (COVERAGE_GAP, SOUNDNESS_GAP); everything else is
non-qualifying. This is a **for-fun leaderboard** — qualifying submissions earn a
place on the public leaderboard, there is no monetary component. For the
untrusted-execution / sandbox requirements of a public deployment see
`docs/contest-security-and-sandbox.md`.

* **REJECT_MALFORMED** — structure check failed (missing src/test/claim/entry) or
  an invalid claim field (bad identifier, out-of-range fuel/slots, malformed args).
* **INVALID** — the claimed behavior does not reproduce on pinned solc+Foundry
  (Forge did not PASS; or an OVER_ACCEPT claim where solc did not reject).
* **REJECTED_OOS** — the reject gate fired (intentional exclusion, or a banned
  cheatcode / cheatcode-address reference in src or test).
* **NEEDS_REVIEW** — Solidus failed *inconclusively* (timeout / resource
  exhaustion), not a clean reject; routed to a human, never auto-qualified.
* **COVERAGE_GAP (lane C)** — Solidus **fails closed** (importer `unimplemented`
  / typecheck / elaboration reject; incl. **over-reject**) on an in-scope,
  solc-accepted program. *Qualifies for the leaderboard.*
* **NO_DIVERGENCE** — Solidus runs and its observable **equals** solc+EVM's (or
  both reject).
* **SOUNDNESS_GAP (lane S)** — Solidus **runs** but the observable **differs**
  (wrong-value / wrong-panic / wrong-revert / revert-vs-success), **or**
  over-accept (Solidus runs a program solc rejects). *Qualifies for the leaderboard.*

**EVM-side observable — precision limit.** v1 takes the solc+EVM observable from
the Forge-**validated** `declared_observable.normal_form` (the Forge test must
PASS first, so the declared value is proven real). v1 does not yet re-parse the
full observable tuple out of Foundry traces; that (and events/state extraction)
is a v1.x refinement. The Solidus side is always recomputed by the Lean `#eval`.

## Dedup (design §6.2)

Every terminal gap gets a **root-cause fingerprint** (not source text):

* lane C: `(fail_stage, fail_reason_class, minimal_node_type_or_field)`
* lane S: `(observable_component, minimal_feature, delta_shape)`

`known_gaps.py` pre-loads G1–G22 (+ H1/H2) fingerprints; a match flags the
verdict `duplicate_of: <id>`. `match_relaxed` gives the maintainer's cluster
hint by minimal-feature token (§6.1d).

## v2 seam — multi-contract (design §3, §8)

`multi_contract.py` documents exactly where v2 plugs in over the existing,
proved open-world seam: (1) contract registry builder, (2) `reflectiveResponder
registry depth` answerer reusing `Contract.callCalldataAtFromWithContext?` +
`snapshotWorld`/`adoptWorld` + the proved adoption round-trip law, (3) the
depth-bounded fold (`DEFAULT_CALL_DEPTH = 1024`), (4) multi-contract observable
extractor (events/state across the subcall tree), (5) retiring `V1-MULTI`. The
v1 single-contract path is the responder-free special case, so v2 is wiring.

## Samples (`contest/samples/`, run via `run_samples.py`)

| Sample | Expected verdict | How validated |
|---|---|---|
| `oos_gasleft` | REJECTED_OOS (X-GASLEFT hidden in a callee) | FULL run (real solc+Foundry+Solidus) |
| `no_divergence` | NO_DIVERGENCE | FULL run |
| `coverage_gap` | COVERAGE_GAP (lane C) | real gate+Forge; Solidus fail-closed **SIMULATED** (marked `synthetic`) |
| `soundness_gap` | SOUNDNESS_GAP (lane S, wrong-value) | real gate+Forge; wrong Solidus observable **SIMULATED** (marked `synthetic`) |

The coverage/soundness Solidus steps are **simulated** because the live gaps
that would drive them are being fixed on sibling branches; the simulation
exercises the exact classifier decision tree with a representative
fail-closed / mismatching Solidus result. `run_samples.py` also unit-tests the
observable comparator and dedup fingerprints directly.
