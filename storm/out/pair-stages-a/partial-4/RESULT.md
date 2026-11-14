# pair-stages-a: partial status 4 (2026-11-14 ~21:05 UTC)

**UniswapV2Pair mint has no end-to-end stage theorem.** The mir5 -> sched
link is blocked: the generator's MIR-to-scheduled-EVM-IR relation cannot cut
inside a called function unless the scheduler records its return address in
the block's layout, so Sched segments carry whole callee bodies and time out
(sched_seg31). The scoped Math.sqrt result of partial-2 remains the only
fully checked deliverable of this lane.

## Inventory (uv2_pair_m, --joins --arms, 8M heartbeats per segment)

Builds on this Hand die when it pauses between turns; runs 1 and 2 ended
that way. Run 3 (Evm1-26) runs inside a turn; numbers below are from it.

| stage | file | result |
|---|---|---|
| stage0 -> mir1 | Defs, Seg2 (207 s), Seg4 (93 s) | built |
| | Seg1 | **failed**: mir1_seg24 whnf timeout |
| | Seg3 | **failed**: mir1_seg52, mir1_seg55 whnf timeout |
| | Seg6 | **failed**: mir1_seg99 (entry of _update) |
| | Seg7 | **failed**: mir1_seg118 (selector dispatch, 26 scope exclusions), 5.1 GB |
| | Seg0, Seg5 | not finished (Hand restart) |
| mir1..mir5 (Mir2-5) | | not built yet |
| mir5 -> sched | Seg1 | **failed**: sched_seg31 (blocker above) |
| sched -> evm1 | Seg1 (260 s), Seg2 (457 s), Seg3 (44 s), Seg4 (97 s), Seg5 (43 s) | built |
| | Seg0 | **failed**: evm1_seg1 whnf timeout |
| evm1 -> evm2 | Defs, Seg0 (149 s), Seg1 (319 s), Seg2 (681 s), Seg3 (45 s), Seg4 (184 s) | all segment files built |
| evm2 -> evm26 | | building / not reached |

No stage-level theorem (Runs/<Stage>.lean) of the pair has a receipt yet,
so no \`#print axioms\` for the pair. Nothing above is claimed beyond the
listed segment files elaborating.

## Next

1. A relation for a return address held below the scheduled layout (unblocks
   mir5 -> sched).
2. The dispatcher and _update-entry segments: cut the dispatcher per
   selector test; split _update's entry segment.
3. Finish Evm3-26 inside turns.

Bundles: unchanged from partial-2.

