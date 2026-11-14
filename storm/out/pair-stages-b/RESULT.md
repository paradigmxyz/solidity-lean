# pair-stages-b: UniswapV2Pair backend stages on getReserves()

Status: delivered against the bases below; rebase onto solidity-lean #166 (f8a4a744) and solar #2637 (902cccc2) pending.

Base: solidity-lean `alpharush/certified-translation` 9fb89ee, solar `alpharush/certified` 38b5232a.
Patches (apply with `git am`):

- `solar-0001-certify-one-selector-scope-and-fuel.patch` (solar 9ac7846e): `certify.py --only SEL=SIG` scopes every stage theorem to one selector with a hypothesis on the calldata word, and `--fuel N` sets the fuel claim. Only crates/verify changes; the compiled bytes are identical to 237518e9.
- `solidity-lean-0001-uniswap-v2-pair-stages.patch`: `scripts/verify/uniswap_v2_pair_stages.sh` (generate, compile, check manifest hashes, write proofs, build one module at a time with receipts, audit axioms; `NEGATIVES=1` builds mutants), `uniswap_v2_pair_mutants.py`, lakefile libs `uv2_gr`, `uv2_grneg`, `uv2_grnegb` (the neg libs must fail; not for CI). Generated files derive from the GPL-3.0 port and are not committed.

Reproduce: `SOLAR_CERTIFY_DIR=<solar>/crates/verify NEGATIVES=1 scripts/verify/uniswap_v2_pair_stages.sh` (default target `uv2_gr=0902f1ac=getReserves()=300`).

## What is proved (edges of docs/CERTIFICATION_TARGET.md)

Program: UniswapV2Pair, `-Ogas --evm-version osaka`, runtime 9321 bytes, sha256 `9107395d75fb33362509951f96504cd35245c0f755624f9b085d86a6542c1411`, 34 stages (stage0, mir1–5, sched, evm1–26).

Scope premise on every theorem: `shr 224 (calldataWord call 0) = 0x902f1ac` (calls of getReserves()). Fuel 300.

| Edge | Status | Theorems |
|---|---|---|
| E4 (MIR→MIR, MIR→EVM IR, EVM IR→EVM IR) | proved, forward simulation, getReserves calls only | `SolarTV.Milestone.Uv2Gr.stage0_ends`, `mir1_run` … `evm26_run`, `stage_*`, composed as `uv2_gr_mir_to_evmir : ∀ o, Stage (mirSem o) (evmirSem o) stage0 evm26 scope` |
| E5 (EVM IR→bytecode) | decoding only | `walk_eq`, `decodes`, `checked`: the bytes decode to evm26. Not execution (see gaps) |
| E3, E6, E7, E8 | not done by this lane | |

Not claimed: backward simulation / refinement composition, other selectors, full-dispatcher equivalence, gas.

## Receipts (fresh scripted run, solar 9ac7846e binary)

Every module exit 0. Stage0/MIR 5–8 s, ≤1.63 GB; Sched 26 s, 1.83 GB; Evm1–26 22–35 s, ≤1.89 GB; Stages 6 s; Assembly 25 s, 2.49 GB. Full log: `receipts.log`. A second full run with `NEGATIVES=1` (14:58–15:19 UTC) repeated every result: `receipts-fresh-negatives.log`, console `fresh-run.log`. Axiom audit (`audit-uv2_gr.txt`): 102 theorems, all within propext, Classical.choice, Quot.sound; no sorry.

Finding: the default fuel (1417572) makes the kernel hit deep recursion in the MIR stages; fuel 300 checks in 5 s. Fuel is part of the stated claim, checked by the proof.

## Negatives (refused by execution, `receipts-neg.log`)

| Mutant | Module | Result |
|---|---|---|
| mir1: getReserves timestamp mask 0xffffffff→0xfffffff | `uv2_grneg.Proofs.Runs.Mir1` | exit 1, 6 s, "sym_exec: the runs end in different results" |
| evm26 same mutation | `uv2_grneg.Proofs.Runs.Evm26` | exit 1, 27 s, same message |
| bytecode byte 832 0xff→0x0f (PUSH4 mask) | `uv2_grnegb.Proofs.Assembly` | exit 1, 15 s, decide refutes the walk |

## Gaps

- E5: Pair bytecode is not call-free (CALL, STATICCALL, RETURNDATASIZE, EXTCODESIZE), so the AssembleNoCall route doesn't apply; StaticRunner is refuted, so a checkCB/checkXB theorem would be vacuous; checkCF needs SitesRun (undischarged) and has no source-side world; `asm_cert.infer` on evm26 fails ("stack heights do not settle").
- sync() / skim(): whole-run sym_exec does not fit. sync stage0: timeout at 8M heartbeats (407 s, 4.2 GB); at 40M aborts at 6 GB (exit 134); a profiling probe also aborted at 6 GB (678 s). sync Evm10: timeout at 8M (505 s, 3.5 GB). Route: scoped cut points (entry relation carries the selector condition, relations restricted to cut points reachable under it). Unvalidated WIP: `wip/cutpoints-mir-reach.patch`, `wip/segment-dsimproc.patch`.
