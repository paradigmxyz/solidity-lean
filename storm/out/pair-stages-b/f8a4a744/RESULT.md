# pair-stages-b on solidity-lean #166 (f8a4a744) and solar #2637 (902cccc2)

Status at 00:20 UTC Nov 15: getReserves() checked end to end on the new base; sync() checks in 22 of 26 stages, 4 open.

Patches (`git am`):
- `solar-0001-fix-certify-no-join-cuts-in-a-scoped-dispatcher.patch` on 902cccc2: under `--exclude`, blocks from which an excluded dispatcher case is reachable are no longer join or segment-bound cut points. A cut there starts from an arbitrary stack word in place of the selector, so the scope's hypotheses cannot prune the excluded functions. Without it, getReserves' `inline-returns` stage (Evm17) times out at 2M heartbeats and fails at 10M ("segments end differently"); with it, Evm17 checks in 80 s. My earlier `--only`/`--fuel` solar patch is dropped: upstream `--exclude`/`--cut` covers it.
- `solidity-lean-0001…`, `solidity-lean-0002…` on f8a4a744: `scripts/verify/uniswap_v2_pair_stages.sh` (scope NAME=SIGNATURE excludes every other Pair function, `--cut --joins --no-mir-joins --segment 8`), mutants, lakefile libs `uv2_gr`, `uv2_sy` and the neg libs (must fail; not for CI).

Program: UniswapV2Pair, `-Ogas --evm-version osaka`, runtime 4446 bytes, sha256 `b8ec7c545bbd4edec1c493cba1975a95b2607573b9563240928938d8dfadbcbc`, 28 stages (stage0, mir1–4, sched, evm1–21), solar 902cccc2.

## getReserves() (uv2_gr): proved

Scope on every theorem: the call's selector word `shr 224 (calldataWord call 0)` is none of the other 26 Pair selectors. Each stage is proved through cut points, both directions (`*_certified`, `*_certified_back`), for any number of loop iterations, composed as `SolarTV.Milestone.Uv2Gr.uv2_gr_mir_to_evmir : ∀ o, Stage (mirSem o) (evmirSem o) stage0 evm21 scope`.

Receipts (`receipts-uv2_gr.log`, scripted run 22:59–23:29 UTC): all 26 stage modules, Stages and Assembly exit 0; MIR 12–13 s at 2.2 GB, Sched 89 s at 2.4 GB, EVM stages 61–93 s at ≤2.06 GB, Assembly 10 s. Axiom audit (`audit-uv2_gr.txt`): 275 theorems, 176 within propext/Classical.choice/Quot.sound, 99 with no axioms, no sorry. The script stopped at its own audit step because it counted only "depends on axioms" lines; it now counts both forms. I checked the counts above by hand. Negatives were not rerun on this base yet.

E5 is still decoded only: the bytes make calls (RETURNDATASIZE in block 2), so the call-free bytes theorem doesn't apply.

## sync() (uv2_sy): 22 of 26 stages check

`receipts-uv2_sy.log`: Mir1, Mir2, Mir4, Evm1, Evm3–5, Evm7–21 exit 0 (34–90 s, ≤2.45 GB). Failing:
- Mir3 (`spell-width-tests`): timeout at 2M and at 12M heartbeats (371 s, 1.85 GB). The pass respells `_update`'s uint112 range check `lt v 2^112 ∧ lt v' 2^112` as `(shr 112 v | shr 112 v') == 0`; the tactic only knows the 160-bit form. `wip-tactic-shr112.patch` adds `shr112_eq_zero` to the simp set (not built yet).
- Sched: entry segment times out at 2M and 12M heartbeats (780 s, 4.0 GB).
- Evm2, Evm6 (`cfg-simplify-early`): timeout at 2M; 12M probe pending.

skim() not started on this base.
