# driver lane (partial, 2026-11-14 15:19 UTC): producer exit status, whole-closure replay, input checks

**Status:** the bundle commit's test suite is green (88 pass, 0 fail, 1 skip by design). The fully cold Counter
certification against solidity-lean 9fb89ee is **still running**: steps 1 to 6 pass, and 6b's full-closure replay
had not run when this was pushed. Nothing here claims Counter is CERTIFIED. `counter-run.md` will hold the
finished run's log, receipt and replay accounting. Nothing has been pushed to paradigmxyz/solar or to any PR
branch.

## What is delivered

- `driver.bundle`: one commit, bcd1ae63e5432d1fffc0b6067afb73c96a498936 (tree 4868389e), on top of
  `alpharush/certified` 38b5232 (the head of #2637, still against feat/lean-solar and not restacked yet, see below).
  `git bundle verify` passes. sha256: ebdce6db471610ad6777f303a22d25b1d5cdbfafacbcc067cd6f3d5b19d0a12b.
- The same commit as a patch, `0001-fix-certify-check-producers-exit-status-and-replay-t.patch`.
- `test.log` and `test.receipt.json`: the suite run on tree 4868389e, with its command, exit code and peak memory.
- `baseline.log`: the same suite at the unmodified 38b5232 (17 pass, `spec-refused` fails), kept for the
  comparison below.

## Changes since 56dd3ce, and why

1. **The red test, fixed honestly.** `spec-refused` expected solar-verify to refuse `uint256[][]`, which it now
   translates (the unmodified spec.sh refuses nothing for it at 38b5232). It is now the positive test
   `spec-nested-supported`: the export is whole, C.f is translated, no function is refused and nothing is left raw.
   Two refusal tests use constructs solar-verify genuinely refuses (checked by running it):
   - `spec-refused-function`: `mapping(uint256 => bool)`, where C.f is left raw ("undeclared symbol") and recorded as refused.
   - `spec-refused-whole`: a struct in a mapping. Its datatype is outside the fragment, so the whole export is
     refused and no VC.lean is written.
2. **No trusted-from-cache or trusted-by-directory modules in the published closure by default.** The driver now
   replays every module of the closure, the toolchain's (Init, Std, Lean) and Mathlib's included, in the run.
   `statuses.replay` reads "all N modules of the published closure replayed by leanchecker in this run" only when
   `replayed == closure` and `trusted == 0`, and `strongest` requires exactly that.
   `CERTIFY_REPLAY_TRUST_UPSTREAM=1` (local only) trusts the toolchain and the upstream packages by directory and
   adds a `provenance:` caveat with their number, which blocks the strongest status. The test
   `lean-replay-accounted` now replays a real 654-module closure in full (654 = 654 + 0, each module listed), and
   `lean-replay-other-module` shows leanchecker output for another module accounts for none of them.
3. **Replay batches (`CERTIFY_REPLAY_BATCH`, default 400).** leanchecker replays a batch's modules in parallel. A
   100-module Mathlib batch peaked at 9.2 GB in one process (161 s, exit 0). This bounds memory and changes nothing
   that is replayed. leanchecker also takes each name as a prefix, so it replays somewhat more than planned; the
   receipt lists those as `replayed_beyond_plan`.
4. **Lake packages are built before the sandbox.** The cold run first failed at the headline
   (`Contracts.Counter.Deploy`) with "read-only file system". The sandboxed steps may write only the root
   package's build, and nothing built the git packages (EthLib, VCVio, cslib, Cli, PolyFun, QuantumFoundations), so
   the driver at 38b5232 has the same gap on a fresh checkout. `guard_build.py packages` lists the package
   modules that the headline, spec and published-statement modules import (24 for Counter). The driver builds them
   before any of the run's own statement or proof modules, as the clean build already does for the vendor
   packages. They are replayed with the rest.
5. **CERTIFY_WRAP** (refuter-6 R7): a non-empty value is now a provenance caveat. The checker and replay already
   ran unwrapped.
6. **The pin moves to solidity-lean 9fb89ee** (alpharush/certified-translation head). 7aedd63 is an ancestor of it,
   and both pin Lean v4.35.0. The toolchain digest is unchanged (tools/certify/toolchain.sha256 matches the
   installed 4.35.0). source_bind.sh's error now says the AST "cannot be bound" instead of "is not this run's
   source": a missing solc gave the latter.
7. The (1) to (3) work of 56dd3ce is unchanged (capture, tree_diff, replay accounting, absolute-path
   toolchain, input checks), apart from the clean build no longer failing on a checkout that has no .lake yet.

## Cold Counter run so far (receipts in counter-run.md when it finishes)

The command (in `~/wt` at tree 4868389e, with target/debug and the git packages' builds removed first):

    CERTIFY_CLEAN_BUILD=1 CERTIFY_REPLAY_BATCH=4 LEAN_NUM_THREADS=2 LEAN_MEMORY=8000 \
      scripts/certify target/certify/solidity-lean/Certified/counter/counter.sol --require-headline --require-final

Earlier attempts this turn, each stopped closed with its own error:

| attempt | stopped at | cause | receipt |
|---|---|---|---|
| 1 | step 6, `Contracts.Counter.Deploy does not check` | read-only file system: unbuilt git packages (fix 4) | exit 1, 699 s, peak 5.0 GB per process |
| 2 | step 6, same module | "(kernel) excessive memory consumption" in SolidCore.Solidity.Interface.Statements at -M 5000 (solidity-lean's lakefile documents peaks up to 5.4 GB) | exit 1, 959 s |
| 3 | step 6b, `the checked source AST of counter cannot be bound` | the pinned solc 0.8.35 was not installed; it is now in ~/.cache/solc, sha256 fa8ac9a3… checked by source_bind.sh, and binds Counter | exit 1, 1382 s, peak 5.3 GB per process, 4.0 GB system |

In attempt 3, every step up to 6b passed, with the headline modules built (Deploy, EndToEnd, Headline), all 23
proof theorems audited to propext, Classical.choice and Quot.sound, the VC export whole (172 lines), and the spec
export whole (48 lines).

## Rebase onto #2637's restack

#2637 is still `alpharush/certified`@38b5232 against `feat/lean-solar`, so there is nothing to rebase onto yet. This
bundle applies to 38b5232 and pins solidity-lean 9fb89ee. When the rebase lane restacks it, I rebase and re-run the
suite and Counter.

## Test suite receipt (tree 4868389e)

```
$ SOLAR=target/debug/solar SOLAR_VERIFY=target/debug/solar-verify tools/certify/test.sh   # solar 66d9c98b (tree 4868389e), Lean (version 4.35.0
ok   unpinned-checkout: is at d77f0c5edf5a2b567e75d4400e5284f14bd900d6, not the pinned 9fb89ee6c4fe68623f033aa9b702714c19e38506
ok   ci-unpinned: CERTIFY_ALLOW_UNPINNED is refused in CI
ok   ci-foreign-solar: CERTIFY_ALLOW_FOREIGN_SOLAR is refused in CI
ok   bad-name: is not lowercase letters
ok   no-source: no such file
skip foreign-solar: /home/hand/solar is built from this checkout
ok   two-contracts: no single contract with runtime code
ok   no-such-contract: has no contract Nope
ok   bytecode-pin: the bytecode is not the pinned Examples/counter/bytecode.hex
ok   not-compiling: solar does not compile
ok   options-empty-line: is not one word of visible characters
ok   options-trailing-space: 'osaka\ ' is not one word of visible characters
ok   options-crlf: is not one word of visible characters
ok   options-empty-file: no solar options
ok   options-driver-flag: emit=asm is set by the driver
ok   options-second-source: extra.sol names a file
ok   options-stray-value: osaka is neither a flag nor the value of one
ok   options-empty-word: '' is not one word
ok   loops-malformed: Examples/counter/loops is not a number
ok   bytecode-pin-empty: the pinned Examples/counter/bytecode.hex is empty
ok   solar-nonzero-after-output: solar does not compile Examples/counter/counter.sol (exit 1)
ok   solar-truncated-json: cannot read solar's output for Examples/counter/counter.sol as its JSON
ok   bytecode-missing: has no runtime bytecode (bin-runtime) for
ok   bytecode-null: has no runtime bytecode (bin-runtime) for
ok   bytecode-empty: the runtime bytecode solar emits for Counter is empty
ok   bytecode-odd-length: is not hex bytes: '608'
ok   bytecode-0x-prefix: is not hex bytes: '0x6080'
ok   exporter-nonzero-after-output: the exporter rejects Counter (exit 3
ok   exporter-bytecode-missing: the export of Counter has no runtime bytecode
ok   legacy-mapfile-hides-status: mapfile < <(producer) read 2 lines of a producer that exits 3 and went on
ok   capture-nonzero-after-output: the producer fails (exit 3)
ok   capture-set-e-inside: the producer fails (exit 1)
ok   capture-pipe-inside: the producer fails (exit 1)
ok   capture-killed: the producer fails (exit 137)
ok   capture-nonempty-empty: the producer prints nothing
ok   capture-ok: captured 2 lines: a b
ok   entries-unreadable: the entries fails (exit 2)
ok   tree-diff-crash: clean_tree fails (exit 2)
ok   tree-diff-silent-exit-1: exit 1 with no difference listed
ok   clean-tree-not-a-checkout: clean_tree.py on a directory that is not a checkout fails (exit 2)
ok   final-record-whole: record accepted
ok   final-record-missing: no record
ok   final-record-empty: final-empty.json is empty
ok   final-record-truncated: final-cut.json is not JSON
ok   final-record-incomplete: lacks theorem, strongest
ok   final-record-no-status: has no status resources
ok   run-record-missing: the run's record /tmp/tmp.3v0zzykYeM/no-record.json is missing or malformed
ok   verify-nonzero-after-output: solar-verify fails on /tmp/tmp.3v0zzykYeM/counter.sol (exit 3)
ok   verify-no-summary: solar-verify exits 1 without its summary line
ok   verify-status-contradicts: solar-verify exits 1 but reports 0 errors
ok   vc-export-truncated: does not end with a newline: it is truncated
ok   vc-export-cut-at-a-line: does not end with 'end T.Counter' (its last line is 'def transcript : String := "(check-sat)\\n"'): it is truncated
ok   vc-export-whole: is whole (17 lines, ends with end T.Counter)
ok   replay-accounted: kernel replay: 3 of 3 modules of the closure outside the trusted directories replayed by leanchecker in this run; 2 trusted by directory (package:/tmp/tmp.3v0zzykYeM/replay/mathlib: 1, toolchain: 1); 0 unaccounted; closure 5 = 3 + 2
ok   replay-include-trusted: kernel replay: 5 of 5 modules of the closure outside the trusted directories replayed by leanchecker in this run; 0 trusted by directory (none); 0 unaccounted; closure 5 = 5 + 0
ok   replay-module-missing: 1 of 3 modules of the closure were not replayed by leanchecker in this run: counter.Shape
ok   replay-checker-silent: 3 of 3 modules of the closure were not replayed
ok   replay-checker-nonzero-after-output: leanchecker exits 1: the kernel replay of the closure fails
ok   replay-trusted-outside-roots: unaccounted for: counter.Shape (/tmp/tmp.3v0zzykYeM/replay/pkg/.lake/build/lib/lean/counter/Shape.olean) is marked trusted but is under no trusted directory
ok   replay-root-not-the-packages: unaccounted for: Evil.X
ok   replay-malformed-line: malformed closure line
ok   replay-duplicate-module: module counter.Shape is listed twice
ok   replay-empty-closure: lists no module of the closure
ok   replay-final-missing: the closure has no module counter.Final
ok   replay-olean-missing: the olean of counter.Shape at /tmp/tmp.3v0zzykYeM/replay/pkg/.lake/build/lib/lean/counter/Gone.olean does not exist
ok   replay-toolchain-checker: kernel replay: 3 of 3
ok   replay-planted-checker: the replay ran /tmp/tmp.3v0zzykYeM/replay/pkg/.lake/build/bin/leanchecker (... not the toolchain's leanchecker
ok   replay-olean-changed: oleans of the closure changed since they were planned: counter.Shape
ok   audit-axiom: axioms beyond propext, Classical.choice and Quot.sound: certify_bad
ok   audit-native-decide: axioms beyond propext, Classical.choice and Quot.sound: uses_native._native.native_decide.ax_1_1
ok   audit-sorry: axioms beyond propext, Classical.choice and Quot.sound: sorryAx
ok   audit-missing: does not check
ok   audit-clean: clean and good pass
ok   scan-bad: the axiom, native_decide and sorry lines are flagged
ok   scan-good: Good.lean passes the scan
ok   lean-replay-accounted: closure: 654 modules, 654 to replay, 0 trusted by directory; kernel replay: 654 of 654 modules of the closure outside the trusted directories replayed by leanchecker in this run; 0 trusted by directory (none); 0 unaccounted; closure 654 = 654 + 0
ok   lean-replay-other-module: 654 of 654 modules of the closure were not replayed
ok   spec-counter: exported, nothing refused
ok   spec-nested-supported: exported, C.f translated, nothing refused (is whole (132 lines, ends with end T.Nested))
ok   spec-refused-function: C.f: undeclared symbol: |m@21|
ok   spec-refused-whole: /tmp/tmp.3v0zzykYeM/structmap.sol (every function): command outside the Lean fragment: (declare-datatypes ((|S.S| 0)) ((
ok   vc-export-real: whole passes, half of it fails: does not end with a newline: it is truncated
ok   spec-export-whole: export: /tmp/tmp.3v0zzykYeM/Spec.lean is whole (48 lines, ends with end T.Counter.Spec)
ok   spec-export-truncated: it is truncated
ok   spec-export-no-end: does not end with 'end T.Counter.Spec'
ok   spec-export-empty: Spec-empty.lean is empty
ok   spec-export-missing: the spec export is missing
ok   spec-export-stale-source: is of a source with SHA-256 2b94af37f654079986183efe0e172cab71445bc30b88f7f1e38a0100490ea427, not
ok   spec-export-other-contract: has no Bundle Token
certify driver tests: all passed
RECEIPT {"command": ["tools/certify/test.sh"], "exit_code": 0, "wall_seconds": 150.2, "max_rss_one_process_mib": 1941, "peak_tree_rss_mib": 1646, "peak_system_used_mib": 2790, "mem_total_mib": 14531, "started_utc": "2026-11-14T15:15:56Z"}
exit status: 0
```

`test.receipt.json`: `{"command": ["tools/certify/test.sh"], "exit_code": 0, "wall_seconds": 150.2, "max_rss_one_process_mib": 1941, "peak_tree_rss_mib": 1646, "peak_system_used_mib": 2790, "mem_total_mib": 14531, "started_utc": "2026-11-14T15:15:56Z"}`

## Proposed publication (waits for Troy's approval)

**Title:** `fix(certify): check producers' exit status and replay the whole closure`

**Commit message** (the bundle commit's, verbatim):

```
fix(certify): check producers' exit status and replay the whole closure

The driver read producers' output with mapfile from a process substitution
and through pipes into command groups, which discards the producer's exit
status: a producer that printed plausible output and then failed was taken as
having succeeded. Every such read now goes through capture
(tools/certify/inputs.sh), which runs the producer as its own job, waits for
it and fails the run unless it exits 0. clean_tree.py exits 2 on any error
instead of 1, and the driver no longer reads its failure as a clean tree.

The kernel replay no longer skips modules replayed by an earlier run or
trusts the toolchain and the upstream packages for their directory. Each run
plans the published statement's whole closure (tools/certify/replay.py), runs
leanchecker --verbose on every module in batches (CERTIFY_REPLAY_BATCH) and
fails unless leanchecker exits 0 and reports replaying each one, with each
olean unchanged. The receipt (closure size, each module and its olean digest,
none unaccounted for) goes into the run's record, and the strongest status
needs all of the closure replayed in the run. CERTIFY_REPLAY_TRUST_UPSTREAM=1
trusts the toolchain and the upstream packages by directory, as a provenance
caveat that blocks the strongest status.

The checker and leanchecker run by absolute path from the toolchain whose
digest tools/certify/toolchain.sha256 records, not as lake env's PATH finds
them and not through CERTIFY_WRAP. A build bin directory in the checkout
fails the run, and a non-empty CERTIFY_WRAP is a provenance caveat.

The lake packages' modules that the headline and the published statement
import are built before the sandboxed steps, which may write only the
package's own build directory; their modules are replayed with the rest.

The run's inputs are checked before use: the solar options, the loops file,
the runtime bytecode (missing, empty, null or not hex) and its pin,
solar-verify's exports (truncated, from another source, a run cut short) and
the published statement's record. tools/certify/test.sh has a case for each,
and its spec cases now test a nested array the fragment supports and two
constructs it refuses. The solidity-lean pin moves to 9fb89ee.
```

**PR description:**

```
The certify driver now fails when any command it reads output from fails, replays every module of the
published statement's closure in every run and accounts for each one, and checks its inputs before using them.

- Exit status: lists read from commands go through capture (tools/certify/inputs.sh) instead of
  mapfile < <(...) and pipes into command groups, which discard the command's status. clean_tree.py exits 2
  on errors, and the driver no longer reads its failure as a clean tree. negative.sh, final_neg.sh,
  regenerated.sh and spec.sh get the same fix.
- Replay: no cache and no module trusted by directory. replay.py plans the whole closure, leanchecker
  --verbose (the toolchain's, by absolute path) replays it in batches, and the run fails unless every module
  is reported replayed with an unchanged olean. The record's replay status lists it, and the strongest status
  needs all of it. CERTIFY_REPLAY_TRUST_UPSTREAM=1 trusts the toolchain and the upstream packages by
  directory, as a caveat that blocks the strongest status.
- Toolchain: the checker and leanchecker run from the toolchain that toolchain.sha256 records, never through
  CERTIFY_WRAP. A build bin directory in the checkout fails the run, and a non-empty CERTIFY_WRAP is a caveat.
- Packages: the lake packages' modules that the headline and the statement import are built before the
  sandboxed steps.
- Inputs: solar options, the loops file, the runtime bytecode and its pin, solar-verify's exports
  (export_check.py) and the published statement's record are checked before use.
- Pin: solidity-lean 9fb89ee.

Tests: tools/certify/test.sh has a case for each (88 pass with Lean 4.35.0, solar and solar-verify on PATH).
```
