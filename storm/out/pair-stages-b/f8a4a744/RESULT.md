# pair-stages-b on solidity-lean #166 (f8a4a744) and solar #2637 (902cccc2)

Status at 09:23 UTC Nov 15: getReserves(), sync() and skim(address) of UniswapV2Pair are proved for every backend stage, from the first lowered MIR to the final EVM IR, scoped to each function's calls and composed. Each also has an exact-bytecode decoding check. Bytecode execution (E5) is not proved.

## Patches (`git am`)
solar on 902cccc2, all in `solar-tv/milestone/cutpoints.py`:
1. 0001 No EVM IR join cuts in a scoped dispatcher. A cut taken before the last excluded selector case loses the selector word.
2. 0002 The scheduled-loop check looks only at loops a call in scope reaches. mint()'s sqrt loop otherwise blocked every stack-scheduling cut for sync() and skim().
3. 0003 Call-constant values at stack-scheduling cuts. A value read by ADDRESS, CALLDATASIZE or CALLVALUE that the scheduler recomputes instead of keeping on the stack is related by a condition `env v = <its word>`. skim() reads ADDRESS, so without this its blocks were never cut. The same commit keeps block cuts out of functions an internal call enters. NOTE: with a cut inside a callee (`sub`, `_safeTransfer`), the MIR segment runs past the callee's cut block while the scheduled one stops there. Why is not understood yet, so callees stay inside their callers' segments.
4. 0004 No stack-scheduling block cuts in the entry (dispatcher) function under `--exclude`. Lowered MIR sets the free memory pointer when a function starts, while the scheduled code sets it in block 0 (or not at all where nothing reads it, as in sync()). So a same-state relation at a dispatcher cut is false.

solidity-lean on f8a4a744:
1. 0001 The stage script and mutants.
2. 0002 Scope by `--exclude` of every other Pair function, with cuts block by block.
3. 0003 Tactic: `cond_and_lt`, `zero_eq_or`, `shr112_eq_zero` (the uint112 range check as `spell-width-tests` writes it); script options `HEARTBEATS`/`LEAN_MEMORY`.
4. 0004 Every scope's Assembly module is audited, and `sym_seg` mismatches count as refusals.
5. 0005 Tactic: `cond_slt`/`cond_sgt` (signed return-data-size checks) and `shr_shl144` (the uint112 mask as `late-word` writes it); lib `uv2_sk`.

Reproduce: `SOLAR_CERTIFY_DIR=<solar with the 4 patches, release binary> NEGATIVES=1 scripts/verify/uniswap_v2_pair_stages.sh "uv2_gr=getReserves()" "uv2_sy=sync()" "uv2_sk=skim(address)"`.

Program: UniswapV2Pair, `-Ogas --evm-version osaka`, runtime 4446 bytes, sha256 `b8ec7c545bbd4edec1c493cba1975a95b2607573b9563240928938d8dfadbcbc`, 28 stages (stage0, mir1–4, sched, evm1–21).

## What is proved
Every theorem in a scope assumes the call's selector word `shr 224 (calldataWord call 0)` is none of the other 26 Pair selectors. That covers calls of the function, plus selectors the Pair does not define, which revert.

Each stage is `Certified` in both directions (`*_certified`, `*_certified_back`) through cut points, for any number of loop iterations. The stages are composed as `SolarTV.Milestone.<Scope>.<scope>_mir_to_evmir : ∀ o, Stage (mirSem o) (evmirSem o) stage0 evm21 scope` (Uv2Gr, Uv2Sy, Uv2Sk). Each Assembly module checks that the exact bytes decode to evm21.

| Scope | Stage modules (Mir1–4, Sched, Evm1–21), Stages, Assembly | MIR | Sched | EVM | Axiom audit |
|---|---|---|---|---|---|
| uv2_gr getReserves() | 26 of 26, exit 0 | 13–14 s, ≤2.2 GB | 89 s, 2.4 GB | 62–97 s, ≤2.1 GB | 275 theorems: 176 within propext/Classical.choice/Quot.sound, 99 none, no sorry |
| uv2_sy sync() | 26 of 26, exit 0 | 33–35 s, ≤2.5 GB | 203 s, 4.2 GB | 60–295 s, ≤3.3 GB | 523: 314 within, 209 none, no sorry |
| uv2_sk skim(address) | 26 of 26, exit 0 | 74–533 s, ≤4.8 GB | 181 s, 4.0 GB | 79–144 s, ≤2.9 GB | 673: 390 within, 283 none, no sorry |

Every module stays within 6 GB. sync's stack-scheduling stage was one 934 s, 6.3 GB segment in the previous delivery; it is now cut.

## Receipts
`receipts.log` records every build of this run (05:58–09:23 UTC). The Hand paused once mid-run (`run-1.log` stops at getReserves' Evm12, with no exit line). The run was then resumed with the same script, skipping regeneration of what was already generated (`run-2.log`, `run-3.log`). Lake reused modules that were already built; those appear as 2 s rebuilds, and the table above uses each module's real build.

In `run-2.log`, sync's stack-scheduling Seg1 failed (07:34, "segments end differently"). It started at a dispatcher cut whose same-state relation is false, which solar patch 0004 removes. `run-3.log` regenerated getReserves' Sched (the only getReserves file 0004 changes) and all of sync and skim, and ends with `SCRIPT_EXIT 0`. The getReserves stages built in `run-1.log` come from files byte-identical to the final generation.

## Negatives (refused by mismatch)
| Mutant | Module | Result |
|---|---|---|
| mir1: getReserves timestamp mask 0xffffffff→0xfffffff | `uv2_grneg.Proofs.Runs.Mir1` | exit 1, 14 s |
| evm21: every PUSH4 0xffffffff → 0x0fffffff | `uv2_grneg.Proofs.Runs.Evm21` | exit 1, 63 s |
| bytecode byte 639 0xff→0x0f | `uv2_grnegb.Proofs.Assembly` | exit 1, 7 s (decide refutes the walk) |

## Gaps
- E5: the bytes make calls (RETURNDATASIZE in block 2), so the call-free bytes theorem doesn't apply. Assembly is decoding only.
- E3, E7 and E8 for the Pair are not done by this lane.
- Cuts inside internal callees are disabled (NOTE in patch 0003); the cause is open.
- Negatives cover getReserves only.
