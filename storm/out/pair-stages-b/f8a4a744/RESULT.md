# pair-stages-b on solidity-lean #166 (f8a4a744) and solar #2637 (902cccc2)

Status at 02:35 UTC Nov 15: getReserves() and sync() are proved for every backend stage from the first lowered MIR to the final EVM IR, scoped to their calls and composed. Each has exact-bytecode decoding; bytecode execution (E5) is not proved. skim() is not started.

## Patches (`git am`)
- solar on 902cccc2: `solar-0001-fix-certify-no-join-cuts-in-a-scoped-dispatcher.patch`. Under `--exclude`, blocks from which an excluded dispatcher case is reachable are never join or segment-bound cuts. A segment starting there has an arbitrary stack word in place of the selector, so the scope's hypotheses cannot prune excluded functions. Without the patch, getReserves' `inline-returns` stage times out at 2M heartbeats and fails at 10M ("segments end differently"). With it, the stage checks in 80 s.
- solidity-lean on f8a4a744, in order:
  1. 0001: the stage script and mutants.
  2. 0002: scope by `--exclude` of every other Pair function, `--cut --joins --no-mir-joins --segment 8`, stage list from the manifest, lib `uv2_sy`.
  3. 0003: `tv/W1Proofs/Tactic.lean` adds `cond_and_lt`, `zero_eq_or` and `shr112_eq_zero`/`zero_eq_shr112` to the procedure's simp set. The script also gains `HEARTBEATS` (default 100M) and `LEAN_MEMORY` (default 8000).
  4. 0004: every scope's Assembly is audited, and `sym_seg` mismatches count as refusals.
- `wip-solar-scoped-loop-check.patch` (not for merge): it restricts the scheduled-loop check to code a call in scope reaches. That cuts sync's Sched stage block by block, but 4 of its segments, starting in `_update`'s block 3 with an arbitrary env, time out at 12M heartbeats. The whole-run Sched below checks, so this patch isn't used.

Reproduce: `SOLAR_CERTIFY_DIR=<solar with the patch> NEGATIVES=1 scripts/verify/uniswap_v2_pair_stages.sh "uv2_gr=getReserves()" "uv2_sy=sync()"`

Program: UniswapV2Pair, `-Ogas --evm-version osaka`, runtime 4446 bytes, sha256 `b8ec7c545bbd4edec1c493cba1975a95b2607573b9563240928938d8dfadbcbc`, 28 stages (stage0, mir1–4, sched, evm1–21).

## What is proved
Every theorem in a scope assumes the call's selector word `shr 224 (calldataWord call 0)` is none of the other 26 Pair selectors. That covers calls of the function, plus selectors the Pair doesn't define, which revert.

Each stage is `Certified` in both directions (`*_certified`, `*_certified_back`) through cut points, for any number of loop iterations. The stages are composed:
- `SolarTV.Milestone.Uv2Gr.uv2_gr_mir_to_evmir`
- `SolarTV.Milestone.Uv2Sy.uv2_sy_mir_to_evmir`

Both have type `∀ o, Stage (mirSem o) (evmirSem o) stage0 evm21 scope`. Assembly modules: the exact bytes decode to evm21.

| Scope | Stage modules | Time and peak memory | Axiom audit |
|---|---|---|---|
| uv2_gr (getReserves) | 26 of 26, Stages, Assembly: exit 0 | MIR 12–13 s at 2.2 GB, Sched 89 s, EVM 61–93 s at ≤2.06 GB | 275 theorems: 176 within the three axioms, 99 with none, no sorry |
| uv2_sy (sync) | 26 of 26, Stages, Assembly: exit 0 | MIR 35 s at 2.46 GB; Sched 934 s at 6.29 GB; Evm2 289 s and Evm6 310 s at ≤3.3 GB; other EVM 70–130 s at ≤2.8 GB | 495 theorems: 286 within the three axioms, 209 with none, no sorry |

Receipts are in `receipts.log`. The scripted run (`run-stages.log`, 01:00–02:26 UTC) built every stage module of both scopes, then stopped at the sync audit step. That was a script bug: it imported Assembly only for the first scope; patch 0004 fixes it. The remaining steps (sync Assembly, both audits, negatives) ran with the same commands in `run-tail.log`, ending in exit 0.

Sync's Sched is a single segment. It checks at 100M heartbeats in 6.29 GB, which is above the 6 GB per-module budget other lanes use.

## Negatives (refused by mismatch)
| Mutant | Module | Result |
|---|---|---|
| mir1: getReserves timestamp mask 0xffffffff→0xfffffff | `uv2_grneg.Proofs.Runs.Mir1` | exit 1, 16 s, "sym_seg: the segments end differently" |
| evm21: every PUSH4 0xffffffff → 0x0fffffff | `uv2_grneg.Proofs.Runs.Evm21` | exit 1, 68 s, same |
| bytecode byte 639 0xff→0x0f | `uv2_grnegb.Proofs.Assembly` | exit 1, 8 s, decide refutes the walk |

The first Mir1 mutant run in the log (02:29) was refused, but the script didn't yet accept `sym_seg`'s message, so it counted as unclassified. The 02:32 rerun counts it.

## Gaps
- E5: the bytes make calls (RETURNDATASIZE in block 2), so the call-free bytes theorem doesn't apply; Assembly is decoding only.
- E3, E7 and E8 for the Pair are not done by this lane.
- skim(): not started on this base.
