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

Driver owner's cold queue, records on solidity-lean alpharush/t1-generic-records @ 216e558e
(Certified/record/):

| case | expected | actual | rejecting check | driver / base |
|---|---|---|---|---|
| Flag (independent held-out positive) | CERTIFIED | REJECTED, exit 1 | published statement's proof: Shape.lean:128 unsolved goals (past-the-end case of `holds_of_getElem` with two connected functions); SpecConnect for raise and lower checked | 20a27f39 / 44572c15 |
| UniswapV2Pair | BLOCKED | BLOCKED, exit 3 | envelope: external call (15x), imports (7x), inheritance (1x), ABI types (6x) | 20a27f39 / 44572c15 |

Flag's rejection is a gap in the driver's proof generator (shape_gen.py), not in Flag or its spec.
It is fixed in solar c167421c, and Flag, SiblingOk and InvOkFlat are queued cold on that commit.
A positive that fails is not a pass: until one certifies, no negative in this table is shown to be
caught by its own fault rather than by the generator. SiblingLeak ran on 20a27f39. If SiblingOk
certifies only on c167421c, the pair is on different pins, and SiblingLeak needs one serial rerun on
c167421c once the queue finishes.

The positive twin, SiblingOk, and the independent held-out positive, Flag, run in the driver
owner's cold queue. The nine replay mutations run only after that queue finishes, against a
certified record, with no other heavy build running. A negative counts as caught by its own fault only when its positive twin
reaches the requested tier, so SiblingLeak's row is final only once SiblingOk certifies on the
same pins.

## Replay cases

`certify --replay DIR` refuses a record directory when any run file differs from the record or an
extra file is present. It then reruns cold and compares every pin. negatives.py's replay cases
(stale bytes, flipped byte, changed solar options, stale spec, stale source, stale import, omitted
selector, false environment pin, out of gas passed off as a revert) edit a copy of a certified
record directory. They run once a held-out contract certifies.
