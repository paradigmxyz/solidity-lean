# pair-stages-a partial-7: UniswapV2Pair `mint`, Sched + Evm1..Evm12 build

Bases: solidity-lean f8a4a744 + pair-stages-b (bundled in partial-5), solar
902cccc2 + pair-stages-b. Generated proofs: `Certified/uv2_pair_m/Proofs`
(`--cut --joins --no-mir-joins --segment 8`, 26 selectors excluded).

## Build receipt

Run b_evm7: `lake -R build uv2_pair_m.Proofs.Runs.Sched uv2_pair_m.Proofs.Runs.Evm1 ... Evm26`,
LEAN_NUM_THREADS=2, `-KleanMemory=6000`, maxHeartbeats 2000000 per theorem.

- Still running when this was written (it had reached Evm12), so there is no
  whole-target exit code yet. It ends non-zero, because of the failures below.
- Peak RSS for one file: 5.5 GB (Sched/Seg9). See peak-rss-kb.txt.
- 130 modules built in this run (built.txt). These add to the modules built in
  earlier runs (partial-6 inventory).

## Stage theorems checked

- `SolarTV.Milestone.Uv2PairM.evm1_certified` / `evm1_certified_back`
  (sched -> evm1): `#print axioms` = [propext, Classical.choice, Quot.sound].
  No sorry (partial-6 axioms-evm1.txt).
- Evm2..Evm12: no stage theorem yet. Every stage still has at least one
  segment that fails, and the stage file refuses to state evmN_certified until
  all its segments build.

## Failing segments (failing.txt, file:line)

- Sched: Seg8:284/318/352/386/420/454 (open leaves: iszero vs `eq _ 0` in the
  relation), Seg9:389/423 (timeout), Seg9:522/556 (open), Seg13:83 (timeout).
- Evm2: timeouts at Seg0:15, Seg4:355/389, Seg6:525, Seg7:15.
- Evm3: timeouts at Seg3:185/219.
- Evm4: Seg3:216/250 open.
- Evm5: Seg2:454/488 and Seg3:46/80 open (eval stuck on a literal Nat
  comparison `15 > 1024`); timeouts at Seg3:151/185 and Seg6:151/185.
- Evm6: Seg4:80/114 open. Evm7: Seg3:284/318 open. Evm8 and Evm9: Seg6:386/420
  open. Evm10 and Evm11: Seg6:114/148 open.
- Evm12 onward: not reached yet.

The open leaves in Evm6..Evm11 sit at the same lines across stages, so they
are likely the same two patterns (iszero/eq mismatch, literal Nat comparisons).

## Status

`mint` has no end-to-end theorem. That needs Sched, Mir1-5 and every Evm
stage to build. MIR stages need the MIR join cuts. In the earlier run Mir2 and
Mir3 timed out on 13 and 14 segments, and Mir1, Mir4 and Mir5 have not been run
on these bases.

Next: normalise `iszero a` to `eq a 0` inside the relation's stack/storage
equalities; a proof-producing step for literal Nat comparisons with small
kernel terms; regenerate the timing-out segments with `--segment 4`.
