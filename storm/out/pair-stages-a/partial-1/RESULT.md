# pair-stages-a: partial status 1 (2026-11-14 ~15:30 UTC)

**No stage theorem for UniswapV2Pair is proved yet.** This drop ships the
work in progress so the integrator can see it. Nothing here should be read as
a proof of any end-to-end MIR->EVM IR stage for the pair.

## Contents

- `solar.bundle` / `solar-patches/`: solar commits on `alpharush/certified` 38b5232ad.
  - 65fc70d5a scope cut-point stages to kept functions: a `Runs/Scope.lean`
    predicate on the call; the entry relation carries `scope call`, so each
    stage, composition and execution theorem is stated only for calls whose
    selector reaches a kept function (here: `mint` and what it calls).
  - bbe87baee prune: join cut points only in kept functions (tail calls
    followed); EVM blocks of excluded functions taken from Schedule.json and
    left out; predecessors paired per split edge; values read from calldata
    related across the two sides.
  - 0d1f1765e (wip) skip excluded functions' call strings; relate one-sided
    live values through calldata reads.
- `sl.bundle` / `sl-patches/`: solidity-lean commits on PR head 9fb89ee.
  - 51d0d39 lakefile libraries for the scoped callsqrt check and the pair.
  - 96c96bd fix: the boolean literal simprocs in `sym_seg` claimed
    `a || false = a` definitionally; the kernel rejected it. They now reduce
    only a literal left operand, and the tests cover the four Bool lemmas.
  - 42d5909 (wip) `seg_case_contra`: closes segment cases whose cut tests
    contradict each other (unit-tested on the conjunction form).

## How the pair port is generated

Flattened port of UniswapV2Pair (not checked in), then

    python3 tools/certify/certify.py gen/UniswapV2Pair --gen-module uv2_pair_m.gen.UniswapV2Pair \
      --proof-dir Proofs --proof-module uv2_pair_m.Proofs --namespace SolarTV.Milestone.Uv2PairM \
      --label uv2_pair_m --joins --heartbeats 8000000 --exclude <every external function but mint>

Kept: mint, _mint, Math.sqrt, SafeMath add/sub/mul, UQ112x112.uqdiv,
_safeTransfer, _update, _mintFee, the revert helper, getReserves, entry.
About 3,200 segments over Mir1..Mir5, Sched, Evm1..Evm26.

## Build receipts so far (Hand: 5 cores, 14 GB; LEAN_NUM_THREADS=2, -M 6000)

| target | result | time | peak RSS |
|---|---|---|---|
| Mir1 Seg1, Seg2, Seg3, Defs | built | 182 s, 265 s, 2 s, 4 s | < 1 GB each |
| Mir1 Seg0 | **failed** (exit 1, 1247 s total) | | 5.7 GB |
| Mir2 Seg1, Seg2, Seg3 | built | 191 s, 269 s, 1 s | |
| Mir2 Seg0 | **failed** (same three segments) | | 5.5 GB |
| Sched Seg2 | **failed**: sched_seg32 whnf timeout at 8M heartbeats | | |

These used the Segment tactic before 42d5909; they must be rebuilt for
final receipts. No `#print axioms` receipt yet because no stage theorem
builds.

## Open failures

1. seg0 (entry): one case where the two segments' cut tests contradict;
   `seg_case_contra` should close it (not yet rebuilt in the pair).
2. Mir seg9: mint's revert-bubbling block (returndatacopy of the whole
   returndata, then revert). whnf of the memory write with a symbolic size
   does not finish at 8M heartbeats, and an unbounded run sat at 1.7 GB for
   17 min. Plan: close identical halts on both sides without reducing the
   write, or stop cutting at terminal join blocks.
3. Mir seg10 (mint bb6 to the _update/_mint path) and sched_seg32: same
   whnf timeout, not yet diagnosed.

## Not in this lane

E5 (assembly) for mint: mint makes staticcalls, and returndatasize lies
outside the executed fragment the current runner covers. burn and the other
external functions are excluded by the `scope` premise.

