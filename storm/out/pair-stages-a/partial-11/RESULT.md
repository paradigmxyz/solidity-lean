# pair-stages-a partial-11: UniswapV2Pair `mint`, build finished; 23 of 26 EVM stage theorems checked

Bases: solidity-lean f8a4a744 + pair-stages-b at e4216d9 (patches in partial-8),
solar 902cccc2 + pair-stages-b. Targets: `uv2_pair_m.Proofs.Runs.Sched`, `Evm1` ... `Evm26`.
LEAN_NUM_THREADS=2, `-KleanMemory=6000`, maxHeartbeats 2000000 per theorem.

## Build receipt

- Final run b_full11 (resumed from the oleans of b_full9/b_full10, which died when the
  Hand paused): `EXIT 1 after 2819s` (exit.txt). It exits non-zero only because of the
  segments under "Failing"; there are no other errors.
- Peak RSS for one file (peak-rss-b_full11.txt): 5.4 GB for Sched/Seg9, which times out.
  The largest file that builds peaks at 3.5 GB (Evm24/Seg6).
- built.txt: 473 modules across the three runs.

## Stage theorems checked (axioms.txt)

`#print axioms` is [propext, Classical.choice, Quot.sound] for all 46 theorems:
`evmN_certified` and `evmN_certified_back` for N = 1, 3, 4, 6-19, 21-26. No sorry in
any Runs/Evm* file. Each stage file also pins this with `#guard_msgs`.
The new ones since partial-10: evm22 inline-returns, evm23 copy-loop-blocks, evm24
cfg-simplify, evm25 loop-layout, evm26 late-word.

## Failing (failing.txt)

- Sched (13/15 segment files): Seg9:389/423 and Seg13:83 time out.
- evm2 cfg-simplify-early (7/8): Seg4:355/389 time out.
- evm5 terminal-dedup (7/8): Seg3:151/185 time out.
- evm20 peephole (17/19): Seg5:525/556 and Seg6:15/46 (one theorem each). Fixed by
  patches/0001: `update_read_same : update m k v k = v` in `seg_cut_test`. The packed
  reserve writes read storage slot 8 back after storing it, and that read stayed
  unreduced. With the lemma both theorems prove alone (leaf-tests/results.txt: 121-123 s,
  2.3-2.4 GB, axioms propext and Quot.sound). The patched Segment.lean elaborates
  (exit 0). It is commit 7f918c4 on pair-stages-d, not yet in a full build.

## Status

`mint` has no end-to-end theorem. Still missing: the Sched stage, evm2, evm5, evm20
(fix ready), and the MIR stages (MIR join cuts). Next: a full rebuild with 7f918c4,
plus smaller segments (`--segment 4`) for the five timing-out segment theorems.
