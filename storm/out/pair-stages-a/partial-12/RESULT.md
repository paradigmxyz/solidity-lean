# pair-stages-a partial-12: rebuild in progress (evm20 fix; evm2/evm5 at --segment 4)

Bases: solidity-lean f8a4a744 + pair-stages-b at 7f918c4 (`update_read_same`,
partial-11 patches/0001 on top of e4216d9), solar 902cccc2 + pair-stages-b. The proofs for
evm2 and evm5 were regenerated with `--segment 4`. Every other stage's proofs are unchanged
(`--segment 8`). Every module rebuilds because Segment.lean changed.

## Build receipt

- b_full12 started 07:31 CST and died when the Hand paused between checks: 102 modules
  built, 0 errors, no exit line.
- b_full13 (same targets, resumed from the built oleans) started 08:20 CST and was still
  running at 09:49 CST. No exit code yet. built-rebuild.txt lists 168 modules across both
  runs.

## Stage theorems rechecked so far on 7f918c4 (axioms.txt)

`evm1_certified`, `evm3_certified` and `evm4_certified`: [propext, Classical.choice,
Quot.sound]. The other stages haven't been rebuilt yet. partial-11 has their receipts
on e4216d9.

## Results so far (failing.txt)

- `--segment 4` doesn't fix evm2 or evm5. In each, the same two theorems still time out
  at 2M heartbeats, now at Evm2/Seg4:457/491 and Evm5/Seg5:253/287.
- Sched Seg9:389/423 and Seg13:83 still time out, as expected: `--segment` only re-cuts
  EVM stages.
- Sched Seg13:83 compiled alone at 8M heartbeats (sched-seg13-8M.log) gets through
  elaboration in 324 s, then the kernel fails with "excessive memory consumption" at
  6 GB. So more heartbeats won't fix the Sched timeouts. They need smaller proof terms.
- evm20 (the slot-8 fix) hasn't been reached in this build yet.

## Status

`mint` has no end-to-end theorem. Open: Sched (3 theorems, kernel memory), evm2 and
evm5 (2 theorems each, timeouts), evm20 (fix awaiting this build), and the MIR stages.
