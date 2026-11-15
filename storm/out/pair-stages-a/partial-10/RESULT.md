# pair-stages-a partial-10: UniswapV2Pair `mint`, 18 EVM stage theorems checked

Bases: solidity-lean f8a4a744 + pair-stages-b at e4216d9 (patches in partial-8),
solar 902cccc2 + pair-stages-b. Run b_full10: `lake -R build uv2_pair_m.Proofs.Runs.Sched
uv2_pair_m.Proofs.Runs.Evm1 ... Evm26`, LEAN_NUM_THREADS=2, `-KleanMemory=6000`,
maxHeartbeats 2000000 per theorem.

## Build receipt

- b_full10 started 03:09 CST and is still running at 06:06 CST (it has reached Evm22).
  No exit code yet. It will end non-zero because of the failures below.
- Peak RSS for one file: 5.6 GB (Sched/Seg9, which times out). The largest file that
  builds peaks at 2.9 GB. See peak-rss-kb.txt.
- built.txt: 374 modules (union of b_full9 and b_full10).

## Stage theorems checked (axioms.txt)

`#print axioms` is [propext, Classical.choice, Quot.sound] for all 36 theorems
(`evmN_certified` and `evmN_certified_back` for each stage below). No sorry in any
Runs/Evm* file. Each stage file also pins this with `#guard_msgs`.

| stage | pass | | stage | pass |
|---|---|---|---|---|
| evm1 | peephole-early | | evm12 | reorder-pushes |
| evm3 | compact-pushes | | evm13 | block-cse |
| evm4 | block-layout | | evm14 | stack-normalize |
| evm6 | cfg-simplify-early | | evm15 | block-layout |
| evm7 | tail-merge | | evm16 | block-layout |
| evm8 | cfg-simplify-early | | evm17 | tail-merge |
| evm9 | tail-merge | | evm18 | block-layout |
| evm10 | outline | | evm19 | block-layout |
| evm11 | cfg-simplify-early | | evm21 | stack-reschedule |

## Not yet checked

- Sched (13/15 segments): Seg9:389/423 and Seg13:83 time out.
- evm2 cfg-simplify-early (7/8): Seg4:355/389 time out.
- evm5 terminal-dedup (7/8): Seg3:151/185 time out. Seg3:151 proved alone in 182 s
  (partial-8) but times out inside the full file.
- evm20 peephole (17/19): Seg5:525 and Seg6:15 time out, and Seg5:556 and Seg6:46 have
  open leaves. These come from the packed reserve writes to storage slot 8. A storage
  read right after a write to the same slot (`update s.storage 8 v 8`) is left
  unreduced, so the prover splits on it. Next: a read-after-write rewrite for `update`.
- evm22-26: not reached yet.

## Status

`mint` has no end-to-end theorem. It still needs Sched, evm2, evm5, evm20 and evm22-26,
plus the MIR stages (MIR join cuts). Next: the `update` read-after-write rewrite, and
`--segment 4` for the timing-out segments.
