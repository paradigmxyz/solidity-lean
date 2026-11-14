# pair-stages-a: partial status 3 (2026-11-14 ~18:40 UTC)

**UniswapV2Pair mint still has no end-to-end stage theorem.** The scoped
Math.sqrt result in partial-2 is unchanged and is still the only fully
checked deliverable of this lane.

## Pair build run 1 (uv2_pair_m, generated with --joins --arms)

Targets Mir1-5 and Evm1-26 on this Hand (LEAN_NUM_THREADS=2, -M 6000, 8M
heartbeats per segment). The Hand restarted during the run, so the run ended
with no exit code; only Mir1 was reached.

| Mir1 file | segments | result |
|---|---|---|
| Defs | | built |
| Seg2 | 17 | built (207 s) |
| Seg4 | 17 | built (93 s) |
| Seg3 | 17 | **failed**: mir1_seg52, mir1_seg55 whnf timeout at 8M heartbeats |
| Seg6 | 17 | **failed**: mir1_seg99 (entry of _update) whnf timeout |
| Seg7 | 10 | **failed**: mir1_seg118 (runtime entry, selector dispatch with 26 scope exclusions) whnf timeout; peak RSS 5.1 GB |
| Seg0, Seg1, Seg5 | 17 each | not reached |

Mir2-5 and Evm1-26: not reached in run 1. Sched: failed earlier
(sched_seg31, whnf timeout).

## Blockers

1. mir5 -> sched: the generator's MIR-to-scheduled-EVM-IR relation can only
   cut inside a called function when the scheduler records its return
   address in the block's layout. For _update, _mint and the other callees
   it does not ("no return address at the loop header of N"), so Sched
   segments carry whole callee bodies (_update has 60 blocks) and time out.
   Needs a relation for a return address held below the recorded layout.
2. MIR-to-MIR segments through _update's entry and through the dispatcher
   time out; the dispatcher case grows with the number of excluded selectors.

Without (1) there is no stage chain from stage0 to evm26 for mint, whatever
the other stages do.

## Running now

Run 2: Mir1 Seg0/1/5 and Evm1-26, to inventory the EVM-to-EVM stages.

Bundles: unchanged from partial-2 (solar 38b5232ad..pair-stages-a, 4 commits;
sl 9fb89ee..pair-stages-a, 3 commits).

