# driver lane: the certify driver checks producer exit status, accounts for the kernel replay, and has negative controls for bad inputs

Base: paradigmxyz/solar `alpharush/certified` at 38b5232add998cd34a311c8cecf5737d38f9cce6.
Delivered: `driver.bundle` (one commit, 2e95a1483a2b7507043f9c1fadc67fe7611f506b, `git bundle verify` passes;
sha256 5981fd8d7dce20d7fa149d5b1a5402497682c94d3e53ab35dcfdb1c077b3e045) and the same commit as
`0001-fix-certify-check-every-producer-s-exit-status-and-a.patch`. It touches only `scripts/certify` and
`tools/certify/`. Nothing has been pushed to solar or to any PR branch.

    git fetch driver.bundle HEAD && git checkout FETCH_HEAD   # on top of 38b5232

Binding target: solidity-lean docs/CERTIFICATION_TARGET.md at a1c3143, edge E6 ("driver byte equality + leanchecker replay")
and "The driver ... replays the closure in the kernel and binds `code`".

## (1) Producer exit status

**Fixed: every list read from a producer goes through `capture`.** It lives in `tools/certify/inputs.sh`, and runs
the producer as its own job with `wait $!`, so `set -e` and `pipefail` hold inside it. The run fails unless the
producer exits 0, and only then is its output read.

Audit of every `mapfile`, `while read`, `< <(...)`, `|| true` and pipe in `scripts/certify`:

| site (38b5232) | what was lost | now |
|---|---|---|
| `mapfile stages/runs < <(ls … \| sed)` | ls failure, so stages were silently missing | `capture_nonempty … lean_modules` |
| `mapfile thms < <(grep … \| awk \| sort \| sed)` | grep error (exit 2) | `capture … proof_theorems` (grep 1 = none, 2 = fail) |
| `mapfile todo < <(python3 … replay keys)` | **a python crash left todo empty, so nothing was replayed and the run printed "ok"** | removed; see (2) |
| `fingerprint: { lean --closure \| awk; find …; } \| sort \| xargs sha256sum` | the group reports only its last command, so a failed closure listing fingerprinted an empty set equally before and after | `fingerprint_files` checks each producer; `closure_oleans` fails on an empty closure; `xargs -r` |
| `closure_fp` (same pipe) | the same | `closure_oleans` |
| `dirty=$(clean_tree.py …) \|\| true` (x2) | a crash (uncaught exception, which exits 1) or a non-git tree read as **clean provenance** | `tree_diff`: 0 and empty means clean, 1 with lines means dirty, anything else fails; clean_tree.py exits 2 on errors |
| `while read … < <(find … -print0)` (CLEAN_BUILD) | find failure | `find … -exec rm -rf {} + \|\| die` |
| `while read m <&3 … 3< certify-order` | an empty order file built nothing | `capture_nonempty order`, and the last module must be NAME.Final |
| `read core_mod … < <(grep \| head)` (spec-connect) | grep error | `capture … entries` |
| `mapfile holds < <(spec_connect.py; echo "exit $?")` | status OK (sentinel line) | `capture` for uniformity |
| `spec_status+="$(grep \| awk \| paste)"` | grep error | `capture_nonempty spec_thms` |
| `mapfile lines < <(cat headline spec 2>/dev/null \| grep -v)` | an unreadable file | existing files only, `capture … entries` |
| `mapfile umods < <(printf \| sort -u)` | (none in practice) | `capture` |
| `read sfile … < <(python3 … source_ast)` | KeyError, so empty arguments went to source_bind | `capture`, exactly one line of three fields |
| `mapfile fmods < <(python3 … proof_module)` | KeyError, so **the proof module was never scanned** | `capture_nonempty` |
| `solar --version \| sed`, `sha256sum \| cut`, `cargo build \| tail`, toolchain digest pipe | exited with no message | explicit `\|\| die` |
| `compile \| bin_runtime` (export) | OK under pipefail, but the message lost the status | status captured on its own and reported |
| `negative.sh` call | set -e exit with no message | `\|\| die` |

The same pattern in the helpers I own: `negative.sh` (`mapfile passes < <(python3 …)`, where a crash silently skipped
every MIR-pass mutation), `final_neg.sh` (`mapfile vmods < <(awk …)`) and `regenerated.sh` (`git status \| grep \|\| true`,
`diff \|\| true`) are fixed. `spec.sh` accepted exit 1 from solar-verify, which a dry run uses for undischarged
obligations. It now also requires solar-verify's closing `verification results::` line, with an error count that
matches the status. Checked and left as they are: `audit.sh`'s `grep … \|\| true` (the per-theorem count check after
it fails closed) and `source_bind.sh`'s `grep -v … \|\| true` (the `cmp` after it fails closed). Outside my lane:
`.github/workflows/ci.yml` loops over contracts with `done < <(grep …)`, which has the same flaw.

## (2) Exhaustive replay accounting

The key-based replay cache is gone: every run replays every module. `tools/certify/replay.py` has two steps:

- **plan:** reads check_final's `MODULE NAME PATH replay|trusted IMPORTS` lines for `NAME.Final`'s closure and decides trust
  again itself. A module is trusted only if its olean is under the toolchain's lib/lean, or under a
  `CERTIFY_TRUSTED_ROOTS` package directory with one of that package's roots. Anything marked trusted that fails this
  test is unaccounted for and fails the run. So does an empty, malformed or duplicate line, a missing olean, or
  `NAME.Final`, `NAME.Statement` or the proof module being absent or trusted.
- **account:** leanchecker runs as `$toolchain/bin/leanchecker --verbose` (it prints `replaying M` per module and exits
  non-zero at the first failure). The run fails unless it exits 0, prints a `replaying` line for every planned module,
  and every olean still has its planned digest. The receipt is written to `.lake/certify-NAME.json.replay` and into
  record.json as `replay` and `statuses.replay`. It holds the closure size, each module replayed with its olean
  sha256, the trusted modules by directory, the checker's path and sha256, and `unaccounted: []`, and the run prints
  the count and the list. `strongest` also requires this receipt.
- `CERTIFY_REPLAY_TRUSTED=1` replays the trusted modules too.

Added after reading storm/out/refuter-6 (R8, R7), because otherwise another program could produce the receipt instead of the toolchain's leanchecker: a lakefile can plant
`.lake/build/bin/leanchecker`, which `lake env` puts first on PATH, and CERTIFY_WRAP wrapped the replay. The checker
and leanchecker now run by absolute path from the toolchain, which must match `toolchain.sha256` (checked from step 5
on, before the first sandboxed build), and they run unwrapped. A `.lake/build/bin` directory outside
`.lake/packages` fails the run. The account step refuses a receipt from any checker other than the toolchain's.

## (3) Negative controls (receipts below)

| input | cases |
|---|---|
| missing/empty bytecode | `bytecode-missing`, `bytecode-null`, `bytecode-empty`, `bytecode-odd-length`, `bytecode-0x-prefix`, `exporter-bytecode-missing`, `bytecode-pin-empty` |
| truncated spec export | `vc-export-truncated`, `vc-export-cut-at-a-line`, `vc-export-real` (real `--dump-lean` output cut in half), `spec-export-truncated` / `-no-end` / `-empty` / `-missing` / `-stale-source` / `-other-contract` (real `--emit-lean-spec` output) |
| missing record | `final-record-missing` / `-empty` / `-truncated` / `-incomplete` / `-no-status`, `run-record-missing`; the driver also requires spec.sh's `refused` record and the replay receipt |
| malformed options | `options-empty-line`, `-trailing-space`, `-crlf`, `-empty-file`, `-driver-flag`, `-second-source`, `-stray-value`, `-empty-word`; `loops-malformed` |
| producer exits non-zero after plausible output | solar: `solar-nonzero-after-output`, `solar-truncated-json`, `exporter-nonzero-after-output`; solar-verify: `verify-nonzero-after-output`, `verify-no-summary`, `verify-status-contradicts`; leanchecker: `replay-checker-nonzero-after-output`; helpers: `capture-*` (exit 3, set -e inside, pipefail inside, SIGKILL), `tree-diff-*`, `clean-tree-not-a-checkout`; `legacy-mapfile-hides-status` shows the old pattern going on after exit 3 |
| replay accounting | `replay-*` (12 synthetic closures), `replay-planted-checker`, and against real Lean 4.35.0: `lean-replay-accounted` (654-module closure: 1 replayed, 653 toolchain), `lean-replay-other-module` |

The driver cases run `scripts/certify` end to end and require a non-zero exit, the error, and no CERTIFIED line. The
bytecode and producer cases use a stand-in solar: an ELF shim compiled at test time, because the driver refuses
scripts. Cases the driver only reaches after Lean (records, replay, spec export) test the helpers it calls.

### Receipts: `tools/certify/test.sh` at this commit's tree (Lean 4.35.0 on PATH, real solar and solar-verify)

The suite ran at cd6c21b, whose tree 7bc64b5a is the tree of the bundle commit 2e95a14 (only the message was amended after).

```
$ SOLAR=target/debug/solar SOLAR_VERIFY=target/debug/solar-verify tools/certify/test.sh   # solar cd6c21bb, Lean (version 4.35.0
ok   unpinned-checkout: is at b7d65107dbe9685f8ca1d9b8836923274146d142, not the pinned 7aedd6330678291a0d13a465ddd398a7990de3a3
ok   ci-unpinned: CERTIFY_ALLOW_UNPINNED is refused in CI
ok   ci-foreign-solar: CERTIFY_ALLOW_FOREIGN_SOLAR is refused in CI
ok   bad-name: is not lowercase letters
ok   no-source: no such file
skip foreign-solar: /home/hand/pyramid-workspace/repos/631030757/target/debug/solar is built from this checkout
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
ok   run-record-missing: the run's record /tmp/tmp.bgf8cAkDsQ/no-record.json is missing or malformed
ok   verify-nonzero-after-output: solar-verify fails on /tmp/tmp.bgf8cAkDsQ/counter.sol (exit 3)
ok   verify-no-summary: solar-verify exits 1 without its summary line
ok   verify-status-contradicts: solar-verify exits 1 but reports 0 errors
ok   vc-export-truncated: does not end with a newline: it is truncated
ok   vc-export-cut-at-a-line: does not end with 'end T.Counter' (its last line is 'def transcript : String := "(check-sat)\\n"'): it is truncated
ok   vc-export-whole: is whole (17 lines, ends with end T.Counter)
ok   replay-accounted: kernel replay: 3 of 3 modules of the closure outside the trusted directories replayed by leanchecker in this run; 2 trusted by directory (package:/tmp/tmp.bgf8cAkDsQ/replay/mathlib: 1, toolchain: 1); 0 unaccounted; closure 5 = 3 + 2
ok   replay-include-trusted: kernel replay: 5 of 5 modules of the closure outside the trusted directories replayed by leanchecker in this run; 0 trusted by directory (none); 0 unaccounted; closure 5 = 5 + 0
ok   replay-module-missing: 1 of 3 modules of the closure were not replayed by leanchecker in this run: counter.Shape
ok   replay-checker-silent: 3 of 3 modules of the closure were not replayed
ok   replay-checker-nonzero-after-output: leanchecker exits 1: the kernel replay of the closure fails
ok   replay-trusted-outside-roots: unaccounted for: counter.Shape (/tmp/tmp.bgf8cAkDsQ/replay/pkg/.lake/build/lib/lean/counter/Shape.olean) is marked trusted but is under no trusted directory
ok   replay-root-not-the-packages: unaccounted for: Evil.X
ok   replay-malformed-line: malformed closure line
ok   replay-duplicate-module: module counter.Shape is listed twice
ok   replay-empty-closure: lists no module of the closure
ok   replay-final-missing: the closure has no module counter.Final
ok   replay-olean-missing: the olean of counter.Shape at /tmp/tmp.bgf8cAkDsQ/replay/pkg/.lake/build/lib/lean/counter/Gone.olean does not exist
ok   replay-toolchain-checker: kernel replay: 3 of 3
ok   replay-planted-checker: the replay ran /tmp/tmp.bgf8cAkDsQ/replay/pkg/.lake/build/bin/leanchecker (... not the toolchain's leanchecker
ok   replay-olean-changed: oleans of the closure changed since they were planned: counter.Shape
ok   audit-axiom: axioms beyond propext, Classical.choice and Quot.sound: certify_bad
ok   audit-native-decide: axioms beyond propext, Classical.choice and Quot.sound: uses_native._native.native_decide.ax_1_1
ok   audit-sorry: axioms beyond propext, Classical.choice and Quot.sound: sorryAx
ok   audit-missing: does not check
ok   audit-clean: clean and good pass
ok   scan-bad: the axiom, native_decide and sorry lines are flagged
ok   scan-good: Good.lean passes the scan
ok   lean-replay-accounted: closure: 654 modules, 1 to replay, 653 trusted by directory; kernel replay: 1 of 1 modules of the closure outside the trusted directories replayed by leanchecker in this run; 653 trusted by directory (toolchain: 653); 0 unaccounted; closure 654 = 1 + 653
ok   lean-replay-other-module: 1 of 1 modules of the closure were not replayed by leanchecker in this run: Good
ok   spec-counter: exported, nothing refused
FAIL spec-refused: nothing refused:
  export: /tmp/tmp.bgf8cAkDsQ/spec-nested/VC.lean is whole (132 lines, ends with end T.Nested)
ok   vc-export-real: whole passes, half of it fails: does not end with a newline: it is truncated
ok   spec-export-whole: export: /tmp/tmp.bgf8cAkDsQ/Spec.lean is whole (48 lines, ends with end T.Counter.Spec)
ok   spec-export-truncated: it is truncated
ok   spec-export-no-end: does not end with 'end T.Counter.Spec'
ok   spec-export-empty: Spec-empty.lean is empty
ok   spec-export-missing: the spec export is missing
ok   spec-export-stale-source: is of a source with SHA-256 2b94af37f654079986183efe0e172cab71445bc30b88f7f1e38a0100490ea427, not
ok   spec-export-other-contract: has no Bundle Token
certify driver tests: 1 failed
exit status: 1
```

**85 pass, 1 fails, and that failure is not from this change.** `spec-refused` expects solar-verify to refuse
`uint256[][] n`, but solar-verify at 38b5232 now translates it. The unmodified 38b5232 suite fails the same case
(baseline.log: 17 pass, `FAIL spec-refused: nothing refused`, exit 1), and the unmodified `spec.sh` refuses nothing for
that file. The fixture needs a construct outside the fragment; I didn't pick one, because that belongs to whoever
owns solar-verify's fragment.

### Full driver run

`scripts/certify Certified/counter/counter.sol --require-headline` with `CERTIFY_CLEAN_BUILD=1` against the pinned
solidity-lean (7aedd63) started on this Hand. Its first attempt got through steps 1 to 4 with the new code
(capture, options, bytecode and export checks, stage list) and then stopped on the Hand's setup: a fresh checkout has
no `.lake/build` for the sandbox to mount without CLEAN_BUILD. The clean-build run is cold-building EvmYul. Its
result, including the real replay receipt, goes to `counter-run.md` in this directory when it finishes; until then the
real-Lean evidence for (2) is the `lean-replay-*` cases above.

## Proposed publication (waits for Troy's approval)

Branch: `fix/certify-producer-status` (or the commit pushed to `alpharush/certified`, as Troy decides).

**Title:** `fix(certify): check every producer's exit status and account for the kernel replay`

**Commit message:** the bundle commit's message, verbatim:

```
fix(certify): check every producer's exit status and account for the kernel replay

The driver read producers' output with mapfile from a process substitution
and through pipes into command groups, which discards the producer's exit
status: a producer that printed plausible output and then failed was taken as
having succeeded. Every such read now goes through capture
(tools/certify/inputs.sh), which runs the producer as its own job, waits for
it and fails the run unless it exits 0. clean_tree.py exits 2 on any error
instead of 1, and the driver no longer reads its failure as a clean tree.

The kernel replay no longer skips modules replayed by an earlier run. Each run
plans the published statement's closure (tools/certify/replay.py), decides
again which modules are trusted by directory, runs leanchecker --verbose on
the rest and fails unless leanchecker exits 0 and reports replaying every
planned module, with each olean unchanged. The receipt (count, list, trusted
modules by directory, none unaccounted for) goes into the run's record.

The checker and leanchecker run by absolute path from the toolchain whose
digest tools/certify/toolchain.sha256 records, not as lake env's PATH finds
them and not through CERTIFY_WRAP, and a build bin directory in the checkout
fails the run.

The run's inputs are checked before use: the solar options, the loops file,
the runtime bytecode (missing, empty, null or not hex) and its pin,
solar-verify's exports (truncated, from another source, a run cut short) and
the published statement's record. tools/certify/test.sh has a case for each.
```

**PR description:**

```
The certify driver now fails when any command it reads output from fails, replays every module of the
published statement's closure in every run and accounts for each one, and checks its inputs before using
them.

- Exit status: lists read from commands go through capture (tools/certify/inputs.sh) instead of
  mapfile < <(...) and pipes into command groups, which discard the command's status. clean_tree.py exits 2
  on errors, and the driver no longer reads its failure as a clean tree. The same pattern is fixed in
  negative.sh, final_neg.sh and regenerated.sh. spec.sh requires solar-verify's summary line.
- Replay: no cache. replay.py plans the closure, decides trust by directory itself, runs the toolchain's
  leanchecker --verbose by absolute path and fails unless every planned module is reported replayed with an
  unchanged olean. The receipt (count, list, trusted modules by directory, none unaccounted for) is in the
  record and its replay status.
- Toolchain: the checker and leanchecker run from the toolchain that toolchain.sha256 records, not as
  lake env's PATH finds them and not through CERTIFY_WRAP. A build bin directory in the checkout fails the run.
- Inputs: solar options, the loops file, the runtime bytecode and its pin, solar-verify's exports
  (export_check.py) and the published statement's record are checked before use.

Tests: tools/certify/test.sh adds 68 cases (85 pass in all with Lean 4.35.0, solar and solar-verify on
PATH). spec-refused already fails on the base commit: solar-verify now translates its fixture.
```
