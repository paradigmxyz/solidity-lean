# Mutation acceptance: the generic driver

The held-out and negative inputs (tests/heldout/) run through solar's generic driver,
`tools/certify/certify`, with no change to the driver or the tree between cases.
[negatives.py](../scripts/verify/mutant/generic/negatives.py) runs the suite and checks that
nothing outside the envelope, and no false input, comes out Certified.

```
python3 scripts/verify/mutant/generic/negatives.py --heldout $PWD/tests/heldout \
  --certify '<solar>/tools/certify/certify {src} natspec --solidity-lean <checkout> --base <sha> --work {work} --record-dir {out}' \
  --replay '<solar>/tools/certify/certify --replay {dir} --solidity-lean <checkout> --work {work}'
```

## Pins of this run

* solar: paradigmxyz/solar alpharush/t1-generic-driver at 9869393976cd5529ff651968273d6b6eb170f244,
  on 902cccc2.
* solidity-lean base bc6da61b.
* solc 0.8.35, Lean 4.35.0.
* The driver's fixed options: `-Ogas --evm-version osaka`.

## Envelope and source-check sweep

The sweep runs `certify SRC natspec --base bc6da61b --prepare-only` per case. That is everything
before the proof run: the solc-AST envelope, the fresh compile and bytecode scan, the gas bound,
the solc-AST front end and the probe of SolidCore's generic source check against the fresh MIR.
"PREPARED" means the case is inside the envelope and goes on to the proof run.

| case | expected | actual (sweep) | rejecting check |
|---|---|---|---|
| Meter | Certified | PREPARED | (proof run by the driver's owner) |
| Gate | Certified | BLOCKED | generic source check: open(): the checked-add guard's tree differs from the MIR's |
| Clamp | Certified or BLOCKED | BLOCKED | constructor parameters (the generic stage deploys with no arguments) |
| Band (renamed, new constants) | Certified or BLOCKED | BLOCKED | generic source check: fit(): source tree undefined (erasure) |
| Registry (entirely new) | Certified or BLOCKED | BLOCKED | generic source check: add(): source tree undefined (erasure) |
| StepSum | Certified or BLOCKED | BLOCKED | loop (no invariant certificate at this base); constructor parameters |
| EmptyRevert | Certified or BLOCKED | BLOCKED | loop |
| ClampWrongSpec | not Certified | BLOCKED | generic source check: clamp(): MIR symbolic run undefined |
| SiblingLeak | not Certified | PREPARED | (proof run) |
| SiblingOk | Certified | PREPARED | (proof run) |
| SiblingFns | not Certified | BLOCKED | generic source check: hi(): MIR symbolic run undefined |
| FalseEnv | not Certified | BLOCKED | generic source check: bump(): checked-add tree differs |
| InitBroken | not Certified | BLOCKED | generic source check: inc(): MIR symbolic run undefined |
| InvBroken | not Certified | BLOCKED | generic source check: inc(): MIR symbolic run undefined |
| MeterWrongSpec | not Certified | PREPARED | (proof run: below) |
| FalseEnvFlat | not Certified | PREPARED | (proof run) |
| InitBrokenFlat | not Certified | PREPARED | (proof run) |
| InvBrokenFlat | not Certified | PREPARED | (proof run) |
| SiblingFnsFlat | not Certified | PREPARED | (proof run) |
| FalseEnvFixed | not Certified | (added after the sweep) | |
| VacuousSecond | not Certified | (added after the sweep) | |
| ExternalCall | BLOCKED | BLOCKED | external call (line 14); several contracts (the interface) |
| Reentrancy | BLOCKED | BLOCKED | external call (`.call`, line 12) |
| Delegatecall | BLOCKED | BLOCKED | external call (`.delegatecall`, line 10); ABI types (`bytes`) |
| Assembly | BLOCKED | BLOCKED | inline assembly (line 10) |

The four unsupported interactions come out BLOCKED from the solc-AST envelope, before any Lean
runs. The negatives the sweep BLOCKs are refused by the source stage's coverage, not by their
fault. They are not evidence that the fault is caught. The *Flat variants and MeterWrongSpec keep
the same fault inside the envelope, so only the proof run can refuse them.

solar-verify's own verdicts on these sources: it refutes MeterWrongSpec, InitBrokenFlat,
InvBrokenFlat and SiblingFnsFlat. It proves FalseEnvFlat (vacuously, under the contradictory
premise), ExternalCall, Reentrancy and Assembly. So the driver must not trust solar-verify's
verdict for the environment premise or for the envelope.

## Proof runs

Cold runs (`CERTIFY_CLEAN_BUILD`, `LEAN_MEMORY=6000`, `LEAN_NUM_THREADS=1`), one at a time.

| case | expected | actual | rejecting check | driver / base | receipt |
|---|---|---|---|---|---|
| SiblingLeak (false ensures `x <= 5 ==> level == 1`; succeeds-if `msg.value == 0`) | REJECTED by its spec | `REJECTED: spec: set_meets0 does not check: omega could not prove the goal: (SpecConnect.lean:67)`, exit 1 | SpecConnect `set_meets0` (the tree of `set` against its exported spec): the fault's own check | solar 20a27f39 / solidity-lean 44572c15 | exit 1, peak 5271 MB, 679 s; record.json status REJECTED, bytecode sha256 707f63a7…, gas bound 2033203 |

The full bundle (record, driver log, pins, digests) is in
[tests/heldout/runs/siblingleak-20a27f39](../tests/heldout/runs/siblingleak-20a27f39/README.md).

Notes on the SiblingLeak run:

* No statement module was built: the run stopped at SpecConnect, before Shape, Final and Statement.
  So no theorem exists to audit with `#print axioms`, and nothing depends on `sorryAx`.
* Earlier attempts gave no verdict. Two were killed by Hand restarts, one on driver 26cbbc78. On
  26cbbc78 the driver printed "spec connected generically" before the kernel had checked
  SpecConnect. A direct `lake env lean` of that generated file failed at `set_meets0` (omega),
  leaving `set_holds` dependent on `sorryAx`. That check is not a control and is not counted.
  Driver 20a27f39 elaborates SpecConnect before naming any theorem, and the verdict above is its
  own.
* The log also shows `scripts/certify: line 775: holds: bad array subscript`. It comes from
  unsetting the last element of an empty array after spec_connect.py exits non-zero. It is harmless
  to the verdict, but it is a shell error on the rejection path.

Driver owner's cold queue, records on solidity-lean alpharush/t1-generic-records @ 039ef8bd
(Certified/record/):

| case | expected | actual | rejecting check | driver / base |
|---|---|---|---|---|
| Flag, acc-flag (independent held-out positive) | CERTIFIED | REJECTED, exit 1 | published statement's proof: Shape.lean:128 unsolved goals (past-the-end case of `holds_of_getElem` with two connected functions); SpecConnect for raise and lower checked | 20a27f39 / 44572c15 |
| Flag, acc2-flag | CERTIFIED | REJECTED, exit 2: `strict tier: flag_4ce5cf9a reached functional, below the requested tier certified (false: provenance_clean, strongest)` | strict tier: provenance (the driver let scripts/certify build solar) and the top-level strongest classification | c167421c / 44572c15 |
| Flag, acc3-flag | CERTIFIED | **CERTIFIED, strict exit 0** | none: every strict component true (published_statement, equivalence, termination, resources, spec, source_bound, provenance_clean, replay_full, strongest); replay closure 3966/3966, trusted 0, unaccounted none; axioms propext, Classical.choice, Quot.sound | 5a9e6bc0 / 44572c15 |
| UniswapV2Pair | BLOCKED | BLOCKED, exit 3 | envelope: external call (15x), imports (7x), inheritance (1x), ABI types (6x) | 20a27f39 / 44572c15 |

acc3-flag's pins: source and spec sha256 4ce5cf9a…, solar binary 91d39457… built at 5a9e6bc0,
options `-Ogas --evm-version osaka`, runtime bytecode sha256 f689833e… (record.json
bytecode_sha256), gas bound 3580203, statement `Certified.flag_4ce5cf9a.Final.final` of shape
`SolidCore.Verify.Generic.Expected` in the fixed environment (caller 0x2000); any-caller is not
covered. The driver owner's fresh-clone `--replay` of this record started at 09:36 CST and is the
last check on it.

Flag's first rejection was a gap in the driver's proof generator (shape_gen.py, fixed in
c167421c); the second was the driver's own provenance (fixed in 5a9e6bc0). Neither was a fault in
Flag or its spec.

**SiblingOk has not certified on any pin yet.** It has not run on 5a9e6bc0, and SiblingLeak ran on
20a27f39, so the pair is not on the same pins. SiblingLeak's row stays provisional until SiblingOk
certifies on 5a9e6bc0 / 44572c15 and SiblingLeak reruns once, serially, on the same pins. Flag
certifying on 5a9e6bc0 shows that a positive inside the envelope reaches the certified tier on that
driver. It does not stand in for SiblingLeak's own twin.

## Replay cases

`certify --replay DIR` refuses a record directory when any run file differs from the record or an
extra file is present. It then reruns cold and compares every pin. negatives.py's replay cases
(stale bytes, flipped byte, changed solar options, stale spec, stale source, stale import, omitted
selector, false environment pin, out of gas passed off as a revert) edit a copy of a certified
record directory. They run once a held-out contract certifies.

They run against acc3-flag's `replay/` (records branch @ 039ef8bd), with
`negatives.py --replay-from DIR` and the driver at 5a9e6bc0
(`tools/certify/certify --replay {dir} --solidity-lean <checkout> --work {work}`). Every case
runs in two layers:

* **file**: one run file of the copy is edited and the manifest (record.json `run_files`) is left
  alone. The driver must refuse the copy before any build.
* **pin**: the run files stay untouched and one pin of record.json is changed. The manifest does
  not hash record.json, so this layer passes the manifest. Only the fresh cold run's comparison of
  `REPLAY_KEYS` can refuse it.

A control (the unedited copy) passes the manifest and starts the fresh cold run. It was stopped at
that point, at the `== replay:` line. Layer file, and the pin cases refused before the fresh run,
ran on 2026-11-15 at 15:41 to 15:42 UTC with no build (each 0 s, no lake or lean process).
Receipts and logs are in
[tests/heldout/runs/replay-acc3-flag](../tests/heldout/runs/replay-acc3-flag/README.md).

| case | layer | change | verdict line | exit | stage |
|---|---|---|---|---|---|
| stale-bytes | file | certify-record.json bytecode replaced by StepSum's fresh runtime bytes | `REJECTED: replay: certify-record.json differs from the record (stale or edited run file)` | 1 | manifest |
| flipped-byte | file | certify-record.json bytecode, middle byte XOR 1 | `REJECTED: replay: certify-record.json differs from the record (stale or edited run file)` | 1 | manifest |
| changed-solar-options | file | inputs/…/options `-Ogas` to `-Osize` | `REJECTED: replay: inputs/Certified/flag_4ce5cf9a/options differs from the record (stale or edited run file)` | 1 | manifest |
| stale-spec-hash | file | Flag.sol: `@custom:ensures true && …` | `REJECTED: replay: Flag.sol differs from the record (stale or edited run file)` | 1 | manifest |
| stale-source | file | Flag.sol: `value = v;` to `value = (v);` | `REJECTED: replay: Flag.sol differs from the record (stale or edited run file)` | 1 | manifest |
| stale-import | file | inputs/…/Source.lean, comment appended | `REJECTED: replay: inputs/Certified/flag_4ce5cf9a/Source.lean differs from the record (stale or edited run file)` | 1 | manifest |
| omitted-selector | file | inputs/…/shape.json, first entry dropped | `REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file)` | 1 | manifest |
| false-env-pin | file | inputs/…/shape.json env `[]` to a caller premise | `REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file)` | 1 | manifest |
| oog-as-revert | file | inputs/…/shape.json gas 3580203 to 1790101 | `REJECTED: replay: inputs/Certified/flag_4ce5cf9a/shape.json differs from the record (stale or edited run file)` | 1 | manifest |
| stale-source | pin | record.json source.sha256, first byte XOR 1 | `REJECTED: replay: the record's source digest is not its source file's` | 1 | source digest, before the fresh run |
| stale-bytes | pin | record.json bytecode_sha256 := sha256 of StepSum's runtime bytes | pending | | fresh run, pin comparison |
| flipped-byte | pin | record.json bytecode_sha256 := sha256 of the flipped bytes | pending | | fresh run, pin comparison |
| changed-solar-options | pin | record.json options `-Ogas` to `-Osize` | pending | | fresh run, pin comparison |
| stale-spec-hash | pin | record.json spec.sha256, first byte XOR 1 | pending | | fresh run, pin comparison |
| stale-import | pin | record.json solidity_lean.inputs_sha256, first byte XOR 1 | pending | | fresh run, pin comparison |
| omitted-selector | pin | record.json functions, first dropped | pending | | fresh run, pin comparison |
| false-env-pin | pin | record.json environment, caller 0x2000 to 0x0 | pending | | fresh run, pin comparison |
| oog-as-revert | pin | record.json gas_bound halved | pending | | fresh run, pin comparison |

The eight pending pin cases each pass the manifest and need the driver's full fresh cold run, which
is heavy. They run serially, one at a time, after the driver owner's fresh-clone replay of the same
record reports.
