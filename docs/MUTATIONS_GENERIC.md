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

The proof run on MeterWrongSpec, started on driver 9869393, was stopped before its verdict: that
driver does not connect the spec. From driver 133a1bb6 the spec is connected: SpecConnect proves
solar-verify's export of the NatSpec, and the published statement includes non-vacuity from one
witness call. In the driver owner's warm run, SpecConnect cannot yet prove Meter's checked-add
postcondition, so Meter and MeterWrongSpec are both refused at SpecConnect. The discriminating
pairs today are those without checked arithmetic: SiblingOk against SiblingLeak and
SiblingFnsFlat, and the flat invariant and environment negatives.

Each proof run is a cold build of the whole closure, so this suite runs one per acceptance run.
Next: SiblingOk, the positive twin, on 133a1bb6. Its record directory also feeds the replay cases.
A negative counts as caught by its own fault only when its positive twin reaches the requested
tier.

## Replay cases

`certify --replay DIR` refuses a record directory when any run file differs from the record or an
extra file is present. It then reruns cold and compares every pin. negatives.py's replay cases
(stale bytes, flipped byte, changed solar options, stale spec, stale source, stale import, omitted
selector, false environment pin, out of gas passed off as a revert) edit a copy of a certified
record directory. They run once a held-out contract certifies.
