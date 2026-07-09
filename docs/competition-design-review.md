# Adversarial Review — Divergence-Contest Design

**Reviewer role:** red-team / adversarial design review of `docs/competition-design.md`
(HEAD `cad10ba`) and the v1 gate harness on `contest/v1-gate-harness`
(`contest/*.py`). Goal: find where the design can be **gamed** (fake win banked),
produce **false positives** (a legitimate submission rejected/mis-laned), or be
**unfair**, before launch.

**Method / confidence tags.** Each finding is marked **CONFIRMED** (verified against
the committed code or a repo probe) or **INFERRED** (reasoned, not executed). Line
references are to the files as read on 2026-07-08.

---

## Executive summary

**Readiness verdict: v1 is NOT launchable as an open, paid, automated contest in its
current form.** Two independent CONTEST-BREAKING defects let an adversary bank a fake
`SOUNDNESS_GAP` leaderboard credit, and a third systematically mis-lanes or mis-pays honest
submissions. All three are **plan-level** (not merely v1 wiring): they follow from
design decisions in §3.4/§4/§5, not from a stub. The multi-contract machinery (§3,
v2) is correctly deferred and not the blocker; the blocker is the *single-contract*
oracle, which is the part §8 calls "a legitimate, launchable contest."

The good news: every defect below has a bounded fix that stays inside the existing
architecture, and the plan's structural spine (whole-submission AST scan, importer
`EXCLUDED_NODE_TYPES` reuse, Forge-must-pass) is sound. With the top-3 fixed and a
manual maintainer sign-off gate on every qualifying verdict, a **restricted** launch
(single-contract, curated invitees, human-in-the-loop) is defensible.

### Top CONTEST-BREAKING risks (fix before any launch)

1. **The EVM-side observable is the submitter's self-declared string, not measured
   from the Forge run** (`adjudicate.py:312-319`, `observable.py:36-41`). The Forge
   test only has to *PASS*; nothing ties the passing test to
   `claim.declared_observable.normal_form`, which is what the comparator actually
   diffs against solidity-lean. An adversary writes a trivially-passing test
   (`assertTrue(true)`) and declares any `normal_form` they like → guaranteed
   mismatch → fake `SOUNDNESS_GAP`. **The oracle is entrant-controlled.** CONFIRMED.

2. **The environment is not pinned across the two engines.** solidity-lean runs the entry
   call from `State.empty` under a zero-valued block/tx env (`Block.lean:110-119`:
   `chainid/number/timestamp/... := 0`; `observable.py:122` passes
   `State.empty` and no `Context`), while Foundry-EVM uses its own non-zero defaults
   (chainid 31337, `block.number` 1, `block.timestamp` 1, a fixed test `msg.sender`
   and `address(this)`). Any submission whose observable reads `block.*`, `msg.sender`,
   `tx.origin`, `chainid`, or `address(this)` **diverges for a non-semantic reason**,
   and there is **no detector** for env-dependent observables (`reject_gate.py` has
   none — grep CONFIRMED). This is the classic differential-testing trap, wide open.
   CONFIRMED.

3. **Foundry cheatcodes in the submitter's test are unrestricted and invisible to the
   gate.** `vm.store`, `vm.prank`, `vm.warp`, `vm.roll`, `vm.deal`, `vm.mockCall`,
   `vm.expectRevert`, `ffi` let the test manufacture the EVM-side state/outcome that
   solidity-lean (run from `State.empty`, no cheatcodes) can never reproduce. The gate scans
   *submission `src/`* ASTs, not the test file, and has no cheatcode detector
   (CONFIRMED). Combined with #1 this is a second, independent way to fabricate a
   divergence. CONFIRMED.

Any one of #1–#3 is sufficient to win the win with a non-bug. Together they mean the
current automated verdict cannot be trusted to qualify.

### Pre-launch checklist (prioritized)

- [ ] **P0 — Measure the EVM observable from the trace, not the claim.** Extract
  outcome/return/revert/events from the Forge run (or a scripted `cast`/`vm.record`
  harness) and *ignore* `declared_observable` for adjudication (keep it only as a
  misreport cross-check). Until then, do not auto-pay any lane-S verdict. (Fix #1)
- [ ] **P0 — Pin one canonical environment on both sides** and thread it into the
  solidity-lean `#eval` (an explicit `Context`/`BlockEnv` = Foundry's defaults), and require
  the Forge test to run under those same pinned values. Reject (or fail-closed) any
  entry call that reads an unpinned env fact. (Fix #2)
- [ ] **P0 — Restrict cheatcodes.** Whitelist only environment-pinning cheatcodes
  (`vm.warp/roll/fee/chainId/prevrandao/deal`) whose effect is *also* applied to the
  solidity-lean context; ban state/oracle-forging cheatcodes (`vm.store`, `vm.mockCall`,
  `vm.prank` beyond the pinned sender, `ffi`, `vm.etch`). Add a test-file AST detector.
  (Fix #3)
- [ ] **P1 — Add an env-observable exclusion/normalizer** to the register (block/tx
  identity, `address(this)`, non-salted create addresses) so env reads are either
  pinned-and-compared or rejected, never silently divergent.
- [ ] **P1 — Make `run_solc_rejects` error-vs-warning and version robust** for the
  OVER_ACCEPT lane (match on solc error *codes* + non-zero exit, not substring
  `"Error:"`). (Finding S3)
- [ ] **P1 — Human sign-off gate** on every qualifying verdict for the initial contest
  window; treat the automated verdict as a *candidate*, not a leaderboard credit.
- [ ] **P2 — Tighten the taint approximation** (function-level co-location is both
  over- and under-inclusive; see G-2) and **fix over-reject/missing-feature
  mislabeling** in `coverage_fingerprint` (stage≠cause; see D-1).
- [ ] **P2 — Close register/importer drift** for the non-`EXCLUDED_NODE_TYPES`
  syntactic detectors (gasleft/msize/storagelayout/fixed are hand-coded and *can*
  drift; only X-ASM/X-IMPORT actually reuse the table). (Finding A-3)
- [ ] **P2 — Deep-fingerprint dedup** (single `_first_token` is collision-prone; see
  D-2) and add a versioned-window check to `is_active` (currently ignores
  `at_version`; Finding D-3).

---

## Findings by attack surface

### Surface 3 + 4 — The oracle & observable-extraction integrity (the core break)

#### O-1 — Entrant-declared EVM observable (CONTEST-BREAKING, plan gap)
**Mechanism that fails:** oracle + observable.
**Scenario.** Submission claims lane S, feature "wrong-value". `test/Divergence.t.sol`:

```solidity
function test_divergence() public { assertTrue(true); }   // PASSES trivially
```

`claim.json`: `declared_observable.normal_form = "success|w:999"`, entry
`Snd.run()` which really returns `w:5`. Adjudicator: step 1 Forge PASS (the test
asserted nothing about `run`); step 2 gate PASS (no excluded feature); step 3 solidity-lean
runs, `observeCall` returns `success|w:5`; comparator diffs `w:5` vs the *declared*
`w:999` → `SOUNDNESS_GAP (wrong-value)`, `pays_out=True`.

**Evidence.** `adjudicate.py:312-321` reads `declared.get("normal_form")` and feeds it
straight to `compare_observables`; the EVM side is never parsed from the Forge run.
`observable.py:36-41` documents this explicitly ("it trusts the Forge-passing claim's
normal-form string"). The `soundness_gap/` sample's own claim says it is *synthetic*
and the value is simulated — i.e. the pipeline has never actually derived an EVM
observable from a trace. CONFIRMED.
**Severity:** CONTEST-BREAKING (lets a bogus win). **Plan or v1?** Plan (§4c/§5.1 make
`declared_observable` the compared value; §3.4 defines the tuple but never says who
*measures* the EVM side — the omission is the bug).
**Fix.** Measure the EVM observable from the Forge execution: a fixed test-harness
entrypoint that performs the declared entry call and emits the outcome/return/revert
via `vm.record`/log capture, parsed by the adjudicator. Diff *that* against solidity-lean.
Keep `declared_observable` only to flag misreports. Do not pay lane S until this lands.

#### O-2 — Codegen/optimizer quirks are attributed to "the language" (HIGH, plan gap)
**Mechanism:** oracle. The adjudicator's EVM side is *compiled bytecode under
Foundry-EVM*, but the contest's intent is solidity-lean vs solc's **language semantics**.
Where solc codegen/optimizer behavior is observable but is not "the language" — e.g.
dirty-high-bits handling of `bytesN`/`uintN` at ABI boundaries, `keccak` of memory a
sub-call left non-zeroed, ordering of side effects the spec leaves unspecified — an
EVM-observed value can differ from a defensible source-semantics reading and be scored
as a solidity-lean *soundness* bug. **Severity:** HIGH (unfair rejections *and* dubious
leaderboard credit). **Plan or v1?** Plan. **Fix.** Publish an "oracle caveats" annex: enumerate
behaviors where solc-EVM is authoritative vs where the source spec is; route disputes
to maintainer review; keep the optimizer **off** (`--optimize` disabled) in the pinned
Foundry profile to shrink the codegen-quirk surface, and pin that in `foundry.toml`.

#### O-3 — solidity-lean-side observable is shape-spoofable via entry selection (MEDIUM, v1)
**Mechanism:** observable. `observeCall` calls `CheckedInput.ownCall … (CallTarget.name
fname)` (`observable.py:101`), resolving by *name* against the imported contract with
`args` rendered from `claim.json` (`observable.py:131-159`, only word/int/bytes forms).
A submitter can point `entry.function` at a *different* overload/name than the Forge
test exercised, or pass args the renderer coerces differently than the ABI encoding the
test used, so the two engines are not evaluating the same call. Nothing cross-checks
that the solidity-lean entry call equals the Forge entry call. **Severity:** MEDIUM (enables
mis-classification; amplifies O-1). **Fix.** Derive the solidity-lean entry call from the
*same* calldata the Forge test sends (selector + ABI-encoded args), not from a
re-rendered `claim.json` arg list.

---

### Surface 1 — Environment non-determinism (the differential-testing trap)

#### E-1 — Unpinned block/tx/self environment (CONTEST-BREAKING, plan gap)
**Mechanism:** oracle/observable. CONFIRMED: `Block.lean:110-119` and `:158-160` give
`BlockEnv.empty`/`TxEnv.empty` all-zero (`chainid=number=timestamp=coinbase=basefee=
prevrandao=gasprice=origin=0`); the contest `#eval` runs `ownCall` with no `Context`
override (`observable.py:115-124`), so solidity-lean sees the zero env, while Foundry uses
chainid 31337, `block.number`/`timestamp` ≥ 1, a fixed sender and computed
`address(this)`.

**Scenario (fake soundness).** `function entry() external view returns (uint) { return
block.number; }`. Real solc+EVM (Foundry): returns `1`. solidity-lean: returns `0`. Comparator
(if O-1 were fixed and the value were measured): `wrong-value` → `SOUNDNESS_GAP`. It is a
**pinning artifact**, not a semantic gap. Same for `block.chainid` (31337 vs 0),
`block.timestamp`, `msg.sender`, `tx.origin`, `address(this)`.

**Scenario (fake coverage / unfair reject).** A legitimate feature test that happens to
read `block.timestamp` in an unrelated assertion becomes non-reproducible or diverges
for the env reason, drowning the real signal.

**Severity:** CONTEST-BREAKING. §6.3 *asks* submitters to pin env via
`vm.warp`/`vm.roll` and declare it, but (a) nothing **enforces** it — there is no env
detector — and (b) even a pinned Forge env is **not propagated to the solidity-lean side**,
which still runs the zero env. **Plan or v1?** Plan (the harness has no env-threading
seam; §3.4 explicitly excludes only gas, not env identity). **Fix.** Define ONE
canonical env, construct a matching `Context`/`BlockEnv` for the solidity-lean `#eval`
(there is a `…WithContext` entry family — `Checked.lean:1316` — to thread it through),
set the identical values in the Forge profile, and add a register entry: an entry-call
observable that depends on any *unpinned* env fact is OOS.

#### E-2 — Create-address / nonce parity (MEDIUM→HIGH for v2, plan gap)
**Mechanism:** observable. §8 already flags this: non-salted `CREATE` address =
`keccak(rlp(sender,nonce))[12:]`; if solidity-lean's allocator and Foundry's nonce model
disagree, any address-valued observable diverges for a non-gap reason. In v1 (single
contract, no `new`) the exposure is small; it becomes real the moment v2 enables
`new C()`. **Fix.** Pin the deployer/nonce model to Foundry's and unit-test address
parity before enabling create-valued observables; keep create2 address OOS (SEM-ADDR).

---

### Surface 2 — Gas leaking into observables indirectly

#### G-1 — Gas-driven control flow smuggled past the taint gate (HIGH, plan+v1)
**Mechanism:** gate. The SEM-GAS/SEM-CLOSEDGAS taint is "excluded quantity appears in a
function that also has an assert/return/emit" (`reject_gate.py:299-360`). It keys on the
*names* `gasleft`/`gasprice` and on `.transfer`/`.send`/`{gas:}`. Two gaps:

- **Out-of-gas as pure control flow with no named quantity.** A callee that reverts
  *only* because it ran out of gas (deep recursion, unbounded loop, a `.call` given a
  tiny gas budget) produces a revert-vs-success divergence with **no `gasleft`
  identifier** anywhere — the detector never fires. solidity-lean does not meter gas, so it
  will *succeed* where EVM OOG-reverts. With O-1/E-1 fixed this is still a clean fake
  `revert-vs-success`. The design even *admits* (§8, open questions) that call
  failure is gas-driven and excluding gas makes some outcomes unpredictable — but no
  detector covers the no-named-quantity case. CONFIRMED (detector list read).
- **`.call{gas: g}` low-level.** `{gas:}` is caught only if the enclosing function also
  has an observed position *and* the option is literally `gas`. A gas budget passed as a
  plain `uint` variable named anything else, or threaded through a helper, evades the
  syntactic option match.

**Severity:** HIGH (a whole class of fake reverts). **Plan or v1?** Both — the plan's
taint is defined syntactically (§1.2), and v1 implements exactly that. **Fix.** Treat
**any** observable that is a revert/OOG whose cause is not a source-level `revert`/
`require`/explicit `Panic` as OOS-suspect and route to review; better, meter a coarse
gas bound in the closed-world run so OOG is at least *modeled* before it is compared.

#### G-2 — Taint over-reject (fairness, v1) and under-reject (gaming, v1)
**Mechanism:** gate. Function-level co-location (`_function_has_observed_position`) is
**both** too strong and too weak. *Too strong (false OOS / unfair):* a function that
logs `gasleft()` to an event for debugging **and** returns an unrelated pure value is
rejected `OUT_OF_SCOPE` though the observed value has nothing to do with gas — the
comparator would have found a real bug. *Too weak (gaming):* split the excluded read and
the assertion across two functions (read gas in `helper()`, store to storage, assert the
stored value in `entry()`) and the per-function scan sees neither function containing
both — the taint never fires, and the gas value reaches the observable. CONFIRMED
(`reject_gate.py:331-360` iterate per-`FunctionDefinition`, no cross-function flow).
**Severity:** MEDIUM (unfairness) + HIGH (gaming vector, compounds G-1). **Fix.** Real
intra-contract def-use/taint across functions and storage, or (pragmatic) escalate any
gas/code/addr *mention anywhere in the reachable submission* to maintainer review rather
than trusting the co-location heuristic to be tight.

---

### Surface 5 — Multi-contract reflective responder (v2)

#### M-1 — Adoption law covers less than closed-world composition needs (HIGH, plan, v2)
**Mechanism:** oracle/soundness of the model. The feasibility argument (§3.2) leans on
`snapshotWorld (adoptWorld w …) = w` "proved in `AdoptionLaws.lean`" and asserts
closed-world composition is "sound by the *same* law that makes reentrancy adoption
sound." The round-trip law is a *faithfulness of the seam* property; it does **not** by
itself establish that arbitrary cross-contract mutation, **delegatecall** (shared
storage / caller-context execution), **selfdestruct** (same-tx account deletion and
balance sweep), value transfer, and multi-level reentrancy compose to the EVM result.
The plan proves the narrow reentrancy case and generalizes by assertion.
**Severity:** HIGH but **v2-only** (v1 is single-contract, `V1-MULTI` enforced —
`reject_gate.py:451-476`, CONFIRMED). **Fix.** Before retiring `V1-MULTI`, state and
discharge (or corpus-pin) composition obligations for delegatecall, selfdestruct, and
nested reentrancy specifically; do not treat the round-trip law as covering them.

#### M-2 — Call-depth/failure without gas (MEDIUM, plan, v2)
**Mechanism:** lane logic. EVM call failure is frequently gas-driven (the 63/64 rule,
OOG at depth), but gas is excluded, so the closed-world run cannot reproduce *why* a
deep call fails; §3.2 substitutes a fixed depth bound of 1024. A submission whose EVM
outcome hinges on the 63/64 forwarding rule (a call that fails on EVM because
insufficient gas was forwarded, not at depth 1024) will diverge from the depth-only
model. **Severity:** MEDIUM, v2-only. **Fix.** Scope v2 to interactions whose outcome is
depth- or logic-determined, not gas-forwarding-determined; add such gas-forwarding
observables to SEM-CLOSEDGAS.

---

### Surface 7 — Coverage-vs-soundness lane boundary

#### L-1 — `solc must reject` is a fragile substring/exit check (MEDIUM, v1)
**Mechanism:** lane logic (OVER_ACCEPT). `run_solc_rejects_source` defaults
`contains="Error:"` (`harness_bridge.py:97-106`) and is entrant-parameterizable via
`claim.solc_reject_contains` (`adjudicate.py:230`). Risks: (a) solc **warnings** contain
other text but the program *compiles* — if a submitter sets `contains` to a token that
appears in a warning while exit code is 0, an accepted-with-warning program could be
mis-read as "solc rejects" and, if solidity-lean runs it, scored as an over-accept soundness
gap; (b) version drift — an error message string in 0.8.35 may differ across patch
builds. **Severity:** MEDIUM (fake over-accept). **Fix.** Require non-zero solc exit
**and** match on a structured solc **error code** (e.g. `TypeError 5887`), not free
text; ignore warnings entirely.

#### L-2 — "solidity-lean runs partially then fails" boundary (LOW–MEDIUM, v1)
**Mechanism:** lane logic. §0/§4 treat "runs to completion" vs "fails closed" as crisp,
but a call that *elaborates and begins executing* then hits an unimplemented construct
mid-run surfaces as a `lean exit != 0` with no marker → classified
`stage="lean"`/`fail_closed` → COVERAGE_GAP (`harness_bridge.py:197-203`). If the same
program *also* would have diverged in value had it completed, the richer soundness signal
is lost, and dedup fingerprints it as an elaboration reject. **Severity:** LOW–MEDIUM
(mis-lane, not a fake win). **Fix.** Distinguish "fail-closed before any effect" from
"partial execution then fail" in the observable normal form; document that partial-run
failures are lane C by rule.

---

### Surface 6 — Dedup fairness

#### D-1 — `stage` is used as a proxy for *cause* (MEDIUM, v1)
`coverage_fingerprint` maps `stage=="run"` → `("typecheck","over_reject",…)` and any
other lean failure → `("elaboration","elab_reject",…)` (`adjudicate.py:141-161`), and
`adjudicate.py:304` sets `sub_kind = "over_reject" if stage=="run" else "missing_feature"`.
But a fail-closed at *execution* can be a genuine **missing feature**, not an
over-reject; the label (and the leaderboard credit weight, §6.4, which scores over-reject *below*
missing-feature) is therefore frequently wrong. **Severity:** MEDIUM (unfair scoring /
mis-dedup). **Fix.** Classify by the importer/typecheck **reason class** already
available (`unimplemented`/`unclassified`/typecheck sentinel), not by which stage
emitted the failure.

#### D-2 — `_first_token` fingerprint collisions (MEDIUM, v1)
Lane-C dedup identity is a single token scraped after `"present:"` or the first
capitalized alnum word (`adjudicate.py:164-181`). Two genuinely different gaps that both
bottom out in, say, `Mapping` produce the same token → **false DUPLICATE** (a real novel
gap denied leaderboard credit). Conversely one root cause reported via two different importer
messages yields two tokens → **false NOVEL** (double leaderboard credit). **Severity:** MEDIUM
(both false-dup and false-novel are unfair/gameable). **Fix.** Fingerprint on the full
`(node_type, field, reason_class)` triple from the importer's structured fail record,
not a scraped word.

#### D-3 — `is_active(at_version)` ignores its argument (LOW, v1)
`ExclusionEntry.is_active` takes `at_version` but returns
`removed_in_version is None` regardless (`exclusion_register.py:87-94`). The §7 fairness
invariant ("judged against the register in force at submission time") is therefore not
actually implemented — if a row is retired mid-contest, *past* submissions re-adjudicated
would use the new register. **Severity:** LOW now (nothing retired yet), becomes real the
first time the register shrinks mid-contest. **Fix.** Implement the semver-window compare
before any register row is retired during a live contest.

---

### Surface 8 — Anti-gaming completeness (exclusion-adjacent slips)

#### X-1 — `X-STORAGELAYOUT` detector is over-broad (LOW, v1)
`detect_storage_layout_specifier` fires on `nodeType=="StorageLayoutSpecifier"` **or**
any node dict merely *containing a key* `"storageLayout"` (`reject_gate.py:241-249`). If
any solc AST node carries a `storageLayout` field for unrelated reasons, a legitimate
submission is falsely `OUT_OF_SCOPE`. **Severity:** LOW (false OOS = one resubmit).
**Fix.** Match the node type / at-clause precisely.

#### X-2 — Register/importer drift only closed for X-ASM and X-IMPORT (LOW–MEDIUM, v1)
The anti-drift guarantee (§7, "syntactic detectors import `EXCLUDED_NODE_TYPES`") holds
**only** for X-ASM/X-IMPORT — the importer's `EXCLUDED_NODE_TYPES` contains *just*
`ImportDirective` and `InlineAssembly` (CONFIRMED, `solc_ast_to_lean_source.py:36`).
X-GASLEFT, X-MSIZE, X-STORAGELAYOUT, X-FIXED-EXEC are **hand-coded** in `reject_gate.py`
and can drift from the importer independently. The design's "cannot drift" claim
over-generalizes. **Severity:** LOW–MEDIUM. **Fix.** State the narrower guarantee, and
add a CI check that each syntactic detector still matches importer behavior.

#### X-3 — Exclusion-adjacent behaviors with no detector (INFERRED, plan)
`extcodesize`/`extcodehash` of not-yet-deployed or `selfdestruct`-ed contracts,
precompile edge outputs (e.g. `ecrecover` malformed-input returning zero,
`modexp`/`identity` sizing), same-tx `selfdestruct` visibility, and function-type ABI
encoding (address+selector) are all exclusion-adjacent (they touch code/address/gas
facts solidity-lean models coarsely) but have **no register entry and no detector**. Each is a
candidate fake-divergence once O-1/E-1 are fixed. **Severity:** INFERRED / medium.
**Fix.** Enumerate these in the register (as OOS or as pinned-and-compared) before
launch; the register is currently silent on all of them.

---

## What the plan gets right

- **Whole-submission AST scan** (§2, `reject_gate.run_gate_on_asts` iterating every
  source) is the correct counter to callee-smuggling and is faithfully implemented.
  CONFIRMED.
- **Reusing the importer's `EXCLUDED_NODE_TYPES`** for X-ASM/X-IMPORT genuinely prevents
  drift *for those two* and is the right pattern (just over-claimed for the rest).
  CONFIRMED.
- **Forge-must-PASS before solidity-lean is consulted** (§4 step 1) correctly rejects
  fabricated *reproductions* — it just does not, by itself, bind the *measured
  observable* (O-1). CONFIRMED.
- **Conservative-taint bias toward OOS** is the right default direction; the problem is
  the approximation's shape (G-2), not the bias.
- **Fail-closed-partition-as-classifier** (§2: `excluded` ⇒ OOS, everything else ⇒
  coverage candidate) is an elegant reuse of the importer's existing discipline.
- **Versioned register that shrinks, never deletes** (`removed_in_version`), and
  pre-loading G1–G22 fingerprints for day-one dedup, are the right fairness instincts —
  they just need the `at_version` compare (D-3) and a stronger fingerprint (D-2) to hold.
- **Deferring multi-contract to v2 behind an enforced `V1-MULTI` guard** is honest and
  correctly scoped; the single-contract v1 really does cover all of G1–G22.

## Overall verdict

The *structure* of the contest is sound; the *oracle* is not yet trustworthy. The three
P0 items (measure-don't-declare the EVM observable, pin-and-thread one environment,
restrict cheatcodes) are the difference between "an adversary can bank a fake win in an
afternoon" and "a defensible differential contest." Fix those three, add a human
sign-off on leaderboard credit for the opening window, and launch **restricted** (single-contract,
optimizer-off, curated entrants). The remaining findings are tractable hardening that can
land during the contest under the versioning discipline the plan already defines.
