# pair-stages-a partial-9: UniswapV2Pair `mint`, full build on the new tactic (in progress)

Bases: solidity-lean f8a4a744 + pair-stages-b at e4216d9 (patches in partial-8),
solar 902cccc2 + pair-stages-b. Targets: `uv2_pair_m.Proofs.Runs.Sched`, `Evm1` ... `Evm26`,
LEAN_NUM_THREADS=2, `-KleanMemory=6000`, maxHeartbeats 2000000 per theorem.

## Build receipt

- b_full9 started 01:47 CST and died when the Hand paused between checks, with no exit
  line: 137 modules built, 0 errors.
- b_full10 (same targets, resumed from the built oleans) started 03:09 CST and is
  still running at 04:06 CST: 47 more modules built. No exit code yet.
- Peak RSS for one file: 5.6 GB (Sched/Seg9, the timing-out file). The largest
  file that builds peaks at 2.9 GB (Evm19/Seg6). See peak-rss-kb.txt.
- built.txt is the union of both runs (182 modules).

## Stage theorems checked (axioms.txt)

`#print axioms` = [propext, Classical.choice, Quot.sound] for all four. No sorry in
Runs/Evm1* or Runs/Evm3*. Each stage file also pins this with `#guard_msgs`.

- `evm1_certified` / `evm1_certified_back` (sched <-> evm1), re-checked on the new tactic.
- `evm3_certified` / `evm3_certified_back` (evm2 <-> evm3, `compact-pushes`): new.

## Segment modules built per stage, so far

Sched 13/15; Evm1 8/8; Evm2 7/8; Evm3 8/8; Evm4 8/8; Evm5 1/8; Evm6-12 0;
Evm13 1/19; Evm14-19 19/19 each; Evm20-26 0 (not reached yet). The stage modules for
Evm4 and Evm14-19 are queued behind the rest of the build.

## Failing (failing.txt)

Only the known timeouts so far, at 2M heartbeats: Sched Seg9:389/423 and Seg13:83,
and Evm2 Seg4:355/389. Evm5 Seg3:185 hasn't been reached yet. Every open leaf from
partial-7 that has been reached so far builds.

## Status

`mint` has no end-to-end theorem. It needs Sched, Evm2 and the rest of the Evm
stages, plus the MIR stages (MIR join cuts). Next: regenerate the timing-out
segments with `--segment 4`, and let b_full10 finish Evm5-13 and Evm20-26.
