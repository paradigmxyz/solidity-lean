# Release candidate 2 (2026-11-16)

Status: **OPEN: 3 of 4 held-out verdicts in, 0 certified.** H2 REJECTED (resource), H3 BLOCKED, H4 REJECTED (the second
draw stays 0/1); H1's first run ABORTED-env (not a verdict), rerun running on 0479b90a since [01:10:47 CST](time:2026-11-16T07:10:47Z). Publisher: the acceptance reviewer (Lane 6), the only publisher of
RC artifacts; one commit per update on `alpharush/rc-2026-11-16`. The first candidate, at driver
800d78a9, stays frozen in `RC.md` as a negative report (0/3 original held-out, 0/1 second draw) and is
history here: nothing in RC2 changes its verdicts.

## Pins

| What | Pin |
|---|---|
| RC2 driver (solar) | `alpharush/t6-getter-fix` @ 0479b90a422245bf77facc51ea17b960ed5c5851. Chain: 800d78a9 → bb626f8a (UTF-8 cut fix: `final_neg.sh`, `generic.py`, `test_generic.py`) → 0479b90a (only `tools/certify/solidity-lean.rev` → 49d1d7f5) |
| solidity-lean base | 49d1d7f5d9b74165486bd9f634202bee1a3633eb (one commit on 44572c15: "fix(spec): read a returned word back in tree_meets"; `Verify/Spec/Tree.lean`, new `Verify/Spec/TreeReturnCheck.lean`, `lakefile.lean`) |
| Held-out set | original draw H1-H3: `alpharush/rc-heldout` @ e0564a28100931a9986af9a848a57bc2bd835c67 (frozen procedure); second draw H4: aa9191531b28e5cd44095f8bd680f789a61729c9 (`draw2/`, closed at H4) |
| Driver test receipts | as reported by T6: `test.sh` exit 0, 88 ok; `test_generic` 32 passed, 1 skipped. Not rerun by the reviewer |

## Run contract (unchanged from RC1)

- The frozen held-out procedure, set e0564a28: one full run per case, no edits to cases, driver or base.
- Record under `Certified/record/rc2-<case>/` with a `MANIFEST.sha256`; report exit, tier reached,
  wall time, peak RSS and the record's commit.
- **Exact-pin rule:** a case is accepted only with certify exit 0 **and** a fresh-clone `--replay` on
  the same driver 0479b90a with all 18 `REPLAY_KEYS` SAME. A replay on any other sha is a
  compatibility check only.
- Tracked keepalive. A run killed by a Hand pause is recorded as **ABORTED** and restarted once; both
  are reported.

## Held-out verdicts

| Draw | Case | Runner | Verdict | Tier | Wall / peak RSS | Record | Replay (exact-pin) |
|---|---|---|---|---|---|---|---|
| original (denominator 3) | H1 SimpleStorage | T6 | pending: rerun running on 0479b90a (record dir `rc2-H1r`). First run **ABORTED-env**, not an H1 verdict (driver exit 1 at 6b, missing package cache; see below) | none | 4309.7 s / 5277 MB largest process, 6180 MB tree | [`Certified/record/rc2-h1-aborted-env/`](https://github.com/paradigmxyz/solidity-lean/tree/a8cb3d29913eb8864ada79f8eda3eab850bf60ce/Certified/record/rc2-h1-simplestorage) | n/a: nothing certified; `--replay` exits 1 |
| original | H2 ViewAndPure | T7 | **REJECTED** (resource, exit 1): stage 6b, Lean exceeded `LEAN_MEMORY=6000` checking `SpecConnect.lean` and segfaulted (exit 139); `add`, `addToX` not connected; not a proof failure. Binary-pin caveat below | none | 2544.2 s / 14.36 GB tree (2 s trace), 13.70 GB largest process | [`Certified/record/rc2-h2/`](https://github.com/paradigmxyz/solidity-lean/tree/315d258e919028fa0cbade40fe6f3beb6a1a2abe/Certified/record/rc2-h2) | n/a: nothing certified; `--replay` exits 1 |
| original | H3 Mapping | T8 | **BLOCKED** (exit 3): generic source check, `myMap(address)` and `remove(address)`: source tree undefined (erasure) | none | 238.5 s / 2.93 GB tree RSS | [`Certified/record/rc2-h3/`](https://github.com/paradigmxyz/solidity-lean/tree/96bd11a1a6dfeb2337c3e50227b6af4f368c6bba/Certified/record/rc2-h3) | n/a: `--replay` exits 1 (BLOCKED, nothing to replay) |
| second (denominator 1, closed) | H4 FunctionModifier | T8 | **REJECTED** (exit 1): no cut points for stage0 to mir1, a recursive call into `@decrement.body` | none | 2.1 s / below the 2 s sampler | [`Certified/record/rc2-h4/`](https://github.com/paradigmxyz/solidity-lean/tree/96bd11a1a6dfeb2337c3e50227b6af4f368c6bba/Certified/record/rc2-h4) | n/a: `--replay` exits 1 (no run files) |

RC1 verdicts at 800d78a9, for comparison only: H1 REJECTED (spec step, `get_meets0`), H2 REJECTED
(resource; spec step times out), H3 BLOCKED (mapping getter and `delete` erasure), H4 REJECTED
(recursion). RC2's base targets H1's returned-word gap; the others are not expected to change unless a
fix for them is in the pin.

**H1 first run: ABORTED-env (R3).** T6's run on 0479b90a (base 49d1d7f5, held-out e0564a28, one
full run, [22:48:34](time:2026-11-16T04:48:34Z) to [00:00:24 CST](time:2026-11-16T06:00:24Z)) exited 1 at stage 6b: `simplestorage_928cc159.Statement does
not check`. The Lean build log shows no proof error. Lake had to build 9 EthLib modules that
`SolidCore.Refinement.Statement` imports (`EthLib.Execution.Proofs.*`, `EthLib.Base.Proofs.MapM`),
which were missing from the `--packages-from` cache, inside the driver's read-only package mount:
`failed to remove output artifacts: read-only file system (error code: 30)`. This is an environment
failure, so it is not counted as an H1 verdict, and one rerun on 0479b90a is pending. What the run
does show: stages 1 to 6 passed, the audit of 26 theorems uses only propext, Classical.choice and
Quot.sound, and stage 6 prints `spec connected generically: set_holds get_holds` (the getter fix
works in the driver). `bytecode_sha256` 6e95f821… equals the 800d78a9 run's.
- **Binary pin (for the rerun):** `record.json` has `solar.commit` 0479b90a, `dirty: false`, but
  `solar.binary_commit` c09510a3 (`binary_sha256` 2df44d25…, the RC1 H1 binary): cargo reused a
  build without re-embedding the commit (`Finished` in 1.04 s). c09510a3..0479b90a changes only
  `tools/certify/`, so the compiler source is the same and the bytecode matches, but the binary-pin
  check fails. The rerun is accepted only with `binary_commit` 0479b90a.

**H1 rerun (in progress, no verdict).** Started [01:10:47 CST](time:2026-11-16T07:10:47Z) on solar
0479b90a (tree e87de259, clean), base 49d1d7f5, into a fresh record dir `rc2-H1r`. The binary was
rebuilt after `cargo clean -p solar-config`: `solar --version` names commit 0479b90a, `binary_sha256`
d472fb30…b2be. Package cache: 24 oleans added, 9519 unchanged (the runner's `CACHE-ADDED.sha256`).
As reported by the coordinator; the reviewer checks these against the record when it lands.

**H2 binary pin (R4).** H2's `record.json` has `solar.commit` 0479b90a, `dirty: false`, but
`binary_commit` 800d78a9 (`binary_sha256` a2e82043…, the RC1 H2 binary; `Finished` in 1.11 s).
`crates/`, `Cargo.toml` and `Cargo.lock` are identical at 800d78a9 and 0479b90a (and at c09510a3),
and `bytecode_sha256` 9ee97f8f… equals RC1's, so the stale embedded commit cannot change a stage-6b
Lean memory failure: the reviewer counts H2 as a REJECTED (resource) verdict on the 0479b90a driver,
with the binary-pin check recorded as failed. A certified record would still need `binary_commit`
0479b90a.

**Base pin receipt (H3, H4).** `Certified/record/rc2-h3/PINS.json:base.commit` and
`Certified/record/rc2-h4/PINS.json:base.commit` = 49d1d7f5d9b74165486bd9f634202bee1a3633eb, at T8's
96bd11a1 and byte-identical here; each `PINS.json` is covered by its record's `MANIFEST.sha256` and
by `RC2.MANIFEST.sha256`. `record.json` itself still names no solidity-lean commit.
- **H4:** `rc2-h4/PINS.json` says the run stopped at the gas bound before it cloned the Lean base, so
  `base.commit` 49d1d7f5 attests the driver's declared dependency (`tools/certify/solidity-lean.rev`
  at 0479b90a), not execution on that base.
- **H3:** the run did clone the base: it reached the solidity-lean front end (its BLOCKED source
  check), which `generic.py` at 0479b90a runs only after checking out the base in its work clone, and
  `rc2-h3/PINS.json` cites that clone's HEAD and tree. The run's own log does not print the
  checked-out commit, so that HEAD is the runner's reading of the clone.

H1 and H2 records are checked for the same key.

## Other records

| Record | Runner | Driver | Verdict | Replay | Accepted |
|---|---|---|---|---|---|
| acc5 (`flag_4ce5cf9a`) | T1 | 0479b90a | **GENERIC CONDITIONAL COMPOSITION** (default context; not a held-out verdict) | pending: exact fresh-clone replay on 0479b90a, all 18 `REPLAY_KEYS` SAME | pending |

acc5 record: T1 `alpharush/t1-generic-records` @ abcd096127559797224a4fdf330dd3476c65b79c,
`Certified/record/rc2-acc5-flag/`. Pending until the exact fresh-clone replay above.

- Final theorem: `Certified.flag_4ce5cf9a.Final.final : Certified.flag_4ce5cf9a.Final.Statement`, the
  expected-type statement (the exact runtime bytes ∧ `Generic.Expected src spec runtimeBytes`);
  assumptions none; axioms `propext`, `Classical.choice`, `Quot.sound`; closure 3966 modules, 0
  trusted; strict tier exit 0. Base pin 49d1d7f5; the run executed solidity-lean 97c1a837 (record
  caveat).
- Scope: a default-context generic conditional composition: one frame, caller 0x2000, contract at
  0x1000, the block and transaction of `Target.message`; runtime bytecode only; valid ABI calls.
  It lacks a Solidity-text/frontend correspondence, so it is **not** universal source-text end to
  end.
- TCB: "source model trusted: SolidCore's checked contract (the solc AST through
  `scripts/solc_ast_to_lean_source.py` and the type checker) is the meaning of the source (frontend
  trust boundary)".
- Not yet run by the reviewer: fresh replay, `--tier lifecycle`, vacuity negatives, tampered replay.

## Addenda carried over (not RC2 verdicts)

- **Counter source-consumer edge** (from RC1 addendum A1), **source-only, OPEN, not closed**: T4 `alpharush/t4-loopvc-rc` @
  e13cda49ed806cd3d35937ae8d9f26cfe357a800 (replayed 675964cc), receipt 34/34, exit 0: the
  expected-type edge for **source semantics only**. Caveats: `replay.sh` builds `Receipt` with
  linked packages (not a full `leanchecker` closure replay); the resource wrapper reads
  `RUSAGE_CHILDREN.ru_maxrss` (largest child, not the whole process tree); the module manifest
  leaves out the transitive source model; not hermetic, no aggregate resource admission, no
  end-to-end claim; compiler solar fd53f637, not the RC2 driver. Aggregate RSS (whole process tree)
  and the transitive manifest stay OPEN; it is a linked-package replay, not a full `leanchecker`
  replay. A later InvOkFlat rerun on the same branch, @ a56262ce871f07e86c02644e32bc820517dfb18b, is
  recorded ABORTED-env and parked; it changes nothing above.
- **E6 any-caller over fresh bytes:** accepted as a post-RC addendum; see the next section. Not
  part of any RC2 verdict.

## Addendum: E6 UniswapV2ERC20.transfer from every caller

Accepted as a post-RC addendum. **It is not an RC2 verdict**: its emitter is solar 697fc686, not the
RC2 driver 0479b90a.

Record: T2 `alpharush/t2-e6-transfer-any-caller` @ 109c6132ce68b559124c26bf0bac85fb3bb9f4dc (on
52152f58): `Certified/uv2_transfer_e6/MANIFEST.md`, `replay/receipt.json` (sha256 5ff89a2c…0ab6) and
`replay/batch-exits.txt`.

| Item | Pin |
|---|---|
| Emitter | solar 697fc6864620d2fdb0b9b3ff66882ae4ad56b41e |
| Spec exporter | solar 902cccc2cb1213219789780a39caf3c1d4d9f35e |
| Port | solar 67946d7d204862c9d28ed18b83604aa00546f5f6 |
| Checkers | solar c09510a39b5c9940845d2c19928c742f676b8675 |
| Base | solidity-lean 4332b47d3495790581a8d0d4f18f690bd8f3d5a6 |

- Closure replay: 11 of 11 batches, `leanchecker` exit 0; 4027 of 4027 modules replayed, 0 trusted,
  0 unaccounted.
- Olean digest 7ddcac87…c818 is identical before and after the replay, over 9906 files.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Scope: runtime tier only. The constructor, lifecycle and reentrancy are out.
- Gas 8199112 is an observed-equality bound (from it on, the bytes' observable equals the
  source's), not a no-out-of-gas claim.
- Exact-input binding receipt: **ACCEPTED (binding scope only)**. Record: T2 @
  7ca76b0b0ee8f532760fe9f1b909e1cf9917a517 (parent 109c6132): `Certified/uv2_transfer_e6/BINDING.md`,
  `binding.json` (result `bound`), `PINS`, `verify_binding.sh`, `verify_binding_negatives.sh`.
  - One raw-byte source identity, 14da00cd…c80b, is shared by the fresh emit, the stage export, the
    solc-AST import and the spec export.
  - The 762294af mismatch is resolved by correspondence: exporting from 14da00cd gives the same 18
    stage modules byte for byte; only `Manifest.lean` differs, and it is outside the closure.
  - Pins are enforced before any comparison, and a mismatch exits 2 naming the pin: source, options,
    solc, emitter (dca17546…), spec exporter (solar-verify), spec, spec applier, importer, importer
    cache, import driver.
  - `verify_binding.sh` exits 0. Negative controls: exit 2 for source, options, solc, emitter and
    spec exporter; exit 1 for runtime bytes, stage, import and spec; exit 0 for the unaltered-copy
    positive control. `verify_binding_negatives.sh` exits 0.
  - No rebuild or replay: it reuses the closure receipt above.
- Not a universal source-text end-to-end claim. TCB unchanged: the solc AST, the importer, the
  port/flattener and the spec export.
- OPEN: aggregate process-tree RSS admission. The summed `leanchecker` RSS peak was measured at
  5.6 GiB; the wrappers were not sampled, so the `leanchecker`-only peak does not close it.
- OPEN: reproducibility of the emitter binary from 697fc686 (one build, one hash).
- OPEN: `importedSourceName` embeds an absolute checkout path; the binding normalizes that one
  string.
- OPEN: the generated GPL files are recorded as hashes only.
- Run history: in the counted run, one task was killed at 00:35 CST during batch 2400 (cause
  unknown). One resume on the same artifacts reran batch 2400 onward. Earlier attempts gave no
  verdict and are not counted.

## Open gaps

- `id(x)`-style returns: a function returning a word (H1's gap) is targeted by base 49d1d7f5; OPEN
  until a held-out case certifies with an exact-pin replay.
- Mapping: the compiler-generated getter of a `public` mapping and `delete` of an element (H3).
- Recursion (H4): admitted by `envelope()`, refused at the gas-need step.
- Constructor / deployment / lifecycle: no tier offered.
- Any caller beyond the fixed one (0x2000) in the generic driver; E6 (addendum above) covers
  `UniswapV2ERC20.transfer` only, on solar 697fc686.
- Loops at MIR, bytes and gas (source-level Counter edge only).
- Counter (e13cda49): source-only; full `leanchecker` replay, aggregate RSS and the transitive
  manifest OPEN.
- Pair: BLOCKED.
- Package cache (driver side): a run's outcome depends on what the `--packages-from` cache holds,
  since a dependency olean missing from the read-only mount surfaces as `Statement does not check`
  (exit 1) instead of an environment error (H1's first run). OPEN.
- Binary pin (driver side): the `solar.binary_commit` field is unreliable while solar's
  [`crates/config/build.rs`](https://github.com/paradigmxyz/solar/blob/0479b90a422245bf77facc51ea17b960ed5c5851/crates/config/build.rs#L29)
  does not track git HEAD for the build the driver makes. The driver runs `cargo build --locked --bin
  solar` (debug profile); build.rs tracks HEAD only when `PROFILE` is not `debug`, and its other rerun
  trigger is `testdata/solidity/CMakeLists.txt` (line 168), so `--version` keeps the commit of the
  build script's first run. `generic.py` at 0479b90a also never compares `binary_commit` with
  `solar.commit`, and `REPLAY_KEYS` hold `binary_sha256`, not the commit. Cargo reused stale binaries
  for H1 (c09510a3) and H2 (800d78a9). T6's H1 rerun forces the pin outside the driver: it runs
  `cargo clean -p solar-config` and exits 94 unless `solar --version` names 0479b90a. OPEN.
- Source digest binding: `generic.py` at 0479b90a computes `source.sha256` from
  `read_text().encode()` (decoded text, re-encoded), while downstream tools reread the path, so the
  source digest is not a raw-byte snapshot binding. OPEN unless a lane shows raw digest identity
  across receipts.

## Receipts

Filled in as verdicts land, each with its record commit and a link.

- **R1, H3 and H4 (T8).** Runner commit [bf8b8a6e](https://github.com/paradigmxyz/solidity-lean/commit/bf8b8a6ed41837f9a1b881262ccbcbeb443d1350) on `alpharush/heldout-rc2-h3-h4` (parent 49d1d7f5); `Certified/record/rc2-h3/` and
  `rc2-h4/` are copied here byte for byte. Checked by the reviewer: both `MANIFEST.sha256` pass
  (manifest sha256 a0d3f1c5… and 9d8f203d…; record.json 7e7a4bcf… and 845680da…); `solar.commit`
  and `binary_commit` are 0479b90a, `dirty: false`; source sha256 b39ab391… equals `Mapping.sol` at
  e0564a28 and 3be4c2f1… equals `draw2/H4-FunctionModifier/FunctionModifier.sol` at aa919153;
  `bytecode_sha256` equals the RC1 records (90714756… and fe2739e8…). Rerun on a 0479b90a checkout:
  `--replay` exits 1 on both records with the messages above, and `--tier lifecycle` exits 2 (tier
  not offered). Wall time and peak RSS come from each run's `receipt.json` (`LEAN_NUM_THREADS=1`,
  tracked keepalive, no Hand pause, no ABORTED run). Caveats: `record.json` does not name the
  solidity-lean commit, so base 49d1d7f5 is the runner's statement (README); each record's
  `MANIFEST.sha256` leaves out its README, which `RC2.MANIFEST.sha256` covers. The pin does not
  change either RC1 verdict: H3's mapping getter and `delete` gap and H4's recursion gap stay open.

- **R2, H3 and H4 pins (T8).** Runner commit [96bd11a1](https://github.com/paradigmxyz/solidity-lean/commit/96bd11a1a6dfeb2337c3e50227b6af4f368c6bba) on top of bf8b8a6e adds only
  `PINS.json` to each record and its line to `MANIFEST.sha256` (4 files, 52 lines). Checked by the
  reviewer: both manifests pass (72bdf35a… and 1e3ad7bc…; `PINS.json` e0dd7747… and 6522b958…);
  `record.json` and every run file are unchanged from R1; the pinned trees equal `git rev-parse` of
  0479b90a (e87de259…) and 49d1d7f5 (69c84f61…), and `solidity-lean.rev` at 0479b90a is 49d1d7f5;
  case sha256 and held-out commits match R1. Verdicts unchanged. R1's caveat that each record's
  manifest leaves out its README still holds.

- **R3, H1 first run (T6), ABORTED-env.** Runner commit [a8cb3d29](https://github.com/paradigmxyz/solidity-lean/commit/a8cb3d29913eb8864ada79f8eda3eab850bf60ce) on
  `alpharush/t6-heldout-records` (parent fe49ed41); its `Certified/record/rc2-h1-simplestorage/` is
  copied byte for byte to `Certified/record/rc2-h1-aborted-env/`, so the rerun's record keeps its own
  name. Checked by the reviewer: `MANIFEST.sha256` (7fa2ce5e…) passes and lists every other file (19);
  `record.json` d04f5777…, `PINS.json` e168b9bd… (`base.commit` 49d1d7f5, driver tree e87de259…);
  `solar.commit` 0479b90a, `dirty: false`, `binary_commit` c09510a3 (above); source sha256
  928cc159… equals `SimpleStorage.sol` at e0564a28; the `not the pinned 49d1d7f5` warning names the
  driver's own inputs commit 27d5c3c1 on the base, as in the RC1 records. Rerun on a 0479b90a
  checkout: `--replay` exits 1 and `--tier lifecycle` exits 2. Wall time and peak RSS come from
  `slot-receipt.json` (`LEAN_NUM_THREADS=1`). T6 labels this run ABORTED-env at
  [e4b493ee](https://github.com/paradigmxyz/solidity-lean/commit/e4b493eef7642b58f4a157611e0f748fa37d6a99)
  on the same branch: `Certified/record/rc2-h1-simplestorage/STATUS.json` has `"label":
  "ABORTED-env"`, `"is_h1_verdict": false`, `"superseded_by": "pending"`. That file is not copied
  here, so `rc2-h1-aborted-env/` stays byte-identical to a8cb3d29.

- **R4, H2 (T7), REJECTED (resource).** Runner commit [315d258e](https://github.com/paradigmxyz/solidity-lean/commit/315d258e919028fa0cbade40fe6f3beb6a1a2abe) on
  `alpharush/heldout-h2-records` (parent e5392be4); `Certified/record/rc2-h2/` is copied here byte
  for byte. Checked by the reviewer: `MANIFEST.sha256` (c6555af1…) passes and lists every other file
  (15); `record/record.json` 3f69d6de…; `solar.commit` 0479b90a, `dirty: false`, `binary_commit`
  800d78a9 (above); `solidity_lean.base` 49d1d7f5 (inputs commit e4706449); source sha256 8c016856…
  equals `ViewAndPure.sol` at e0564a28; no read-only or error-code-30 line, so not the H1 cache
  failure. Rerun on a 0479b90a checkout: `--replay` exits 1 and `--tier lifecycle` exits 2. Wall time
  and peak RSS from `receipt.json`, `memtrace.tsv` and `time-v.txt` (`LEAN_NUM_THREADS=1`, started
  [23:20 CST](time:2026-11-16T05:20:18Z)). An earlier launch at 22:49 CST never started certify
  (`/usr/bin/time` missing, exit 127): not a run.

## Files

- `RC.md`: the frozen RC1 report (800d78a9), unchanged from b83d7526.
- `RC2.md`: this file. `RC2.MANIFEST.sha256` covers this file and every file under
  `Certified/record/rc2-*`.
- `Certified/record/rc2-h3/`, `Certified/record/rc2-h4/`: T8's records, byte-identical to 96bd11a1.
- `Certified/record/rc2-h2/`: T7's H2 record, byte-identical to 315d258e.
- `Certified/record/rc2-h1-aborted-env/`: T6's ABORTED-env H1 run, byte-identical to
  `rc2-h1-simplestorage/` at a8cb3d29.
