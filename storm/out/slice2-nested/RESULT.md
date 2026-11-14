# slice2-nested: UniswapV2ERC20 approve and transferFrom (checkpoint 3: certified)

Base: solidity-lean PR #166 head f8a4a74 (transfer certified at 0x2000, any-caller backend), which
already contains this lane's earlier work as d0ab5d6 (approve and transferFrom: E3, the exact source
specs, the key-level corollaries, the E3 negative controls). This checkpoint is one commit on top:
a2fa4bb "feat(uniswap-v2): certified approve, transferFrom" (sl-patches/0001, bundle
sl-slice2-nested-e4.bundle, range f8a4a74..a2fa4bb). The checkpoint 1 and 2 patches and bundle that
were here are superseded (merged as d0ab5d6) and removed from this folder; they stay in this
branch's history.

solar: PR #2637 head 902cccc2 built; it differs from the pinned stages rev 697fc68
(scripts/verify/uniswap_v2_stages-solar-rev) only in certify tooling it does not use here
(certify.py, gen_ctxgas.py, asm_ctx.py identical), so the scripts ran against a 697fc68 checkout
with that binary. Pinned source sha256 14da00cd...ac80b; runtime 1183 bytes, sha256
ca4c1925...0a0b, the same bytes as transfer's (`CtxGasA.code_eq`, `CtxGasTF.code_eq`: `rfl`).

No GPL-derived file is in the patch: the stages, certificates and proofs generated from the port
(CtxGasA/TF.lean, ProofsA/, ProofsTF/, gen/, Nested/Trees.lean) are generated at build and
gitignored.

## Statements

```lean
-- Contracts/UniswapV2/ERC20/Certified/Approve.lean
theorem Approve.certified : ∃ c, contract? = .ok c ∧
    Certified (solidCore fuel) c code ApproveValid Allowed ApprovePost (fun _ => 5856506)
-- Allowed := success ∨ output = []   (a spender word ≥ 2^160 reverts with no data)

-- Contracts/UniswapV2/ERC20/Certified/TransferFrom.lean
theorem TransferFrom.certified : ∃ c, contract? = .ok c ∧
    Certified (solidCore fuel) c code TransferFromValid Allowed TransferFromPost (fun _ => 15558412)
-- Allowed := success ∨ output = [] ∨ output = subUnderflow ∨ output = addOverflow
```

Same shape as `Certified.Transfer.certified`: inhabited, equivalence at every gas, termination
with the allowed statuses, the postcondition of every source run, resources (from G gas on the
bytes give exactly the source's result). Caller 0x2000, as for transfer.

**No hash premise** in either: `ApproveValid` / `TransferFromValid` are the generic stage's valid calls
(any argument words, no value, any storage listing the deployed DOMAIN_SEPARATOR slot), and
`ApprovePost` / `TransferFromPost` say the result is exactly `approveResult` / `transferFromResult`
of the call's storage and words (sequential slot updates in source order). The scoped premise
(`HashScopeNested.Scoped` on the call's footprint) enters only the key-level corollaries on the bytes.

On the bytes (from the gas bound on, `Final.Target.runWith`):
- `Approve.approve_bytes`: exactly `approveResult (slotValue σ) spender value`.
- `Approve.approve_keys_bytes` (scoped premise): a clean call succeeds, sets allowance[caller][spender], leaves every slot below 2^128 unchanged.
- `TransferFrom.transferFrom_bytes`: exactly `transferFromResult (slotValue σ) frm dst value`.
- `TransferFrom.self_max_bytes` (required case, scoped premise): balance 2^256-1, infinite allowance, `transferFrom(frm, frm, 1)` succeeds and the balance stays 2^256-1.
- `TransferFrom.self_short_bytes` (required case, scoped premise): a self-transfer above the balance reverts.

## Edge status

| Edge | approve | transferFrom |
|---|---|---|
| E1 frontend | TRUSTED (shared with transfer) | same |
| E3 source -> stage0 | PROVED (d0ab5d6) `check_approve_ok` | PROVED (d0ab5d6) `check_transferFrom_ok` |
| E4 stage0 -> evm11 | **PROVED** `SolarTV.Milestone.Uv2Erc20A.uv2_erc20_approve_mir_to_evmir`, 16 stages, every oracle | **PROVED** `SolarTV.Milestone.Uv2Erc20TF.uv2_erc20_transferFrom_mir_to_evmir`, 16 stages, every oracle |
| E4 any caller | **PROVED** `AnyCaller.Approve.stages_from`, `backend_any_caller`, `resources_any_caller` | **PROVED** `AnyCaller.TransferFrom.*` |
| E5 + E8 bytes, gas | **PROVED** `CtxGasA.gas_edge`, G = 22100·(5·53)+6 = 5856506 | **PROVED** `CtxGasTF.gas_edge`, G = 22100·(11·64)+12 = 15558412 |
| E5 negative controls | **PROVED** `CtxGasA.rejects_jump`, `rejects_sstore` (allowance SSTORE at 0x1e0 as POP) | **PROVED** `CtxGasTF.rejects_jump`, `rejects_sstore` (allowance SSTORE at 0x2b1 as POP) |
| E7 spec | PROVED `approve_meets` (d0ab5d6), carried to the bytes here | PROVED `transferFrom_meets` (d0ab5d6), carried to the bytes here |
| Composition | **PROVED** `Approve.certified` | **PROVED** `TransferFrom.certified` |

Status: CERTIFIED at the caller 0x2000, same scope and trust base as transfer (E1 trusted; the
source side fixes the caller; the backend and gas edges hold from any caller).

## How it was generated

```
scripts/verify/uniswap_v2_gen.sh
SOLAR_DIR=<solar at 697fc68, built> scripts/verify/uniswap_v2_stages.sh
python3 scripts/verify/uniswap_v2_stage0_mutants.py      # for Nested/NegE3
scripts/verify/uniswap_v2_stages_nested.sh               # new
lake build -KleanMemory=6000 uv2_erc20 ContractsUniswapV2ERC20Nested ContractsUniswapV2ERC20Certified
```

Three things differ from transfer's recipe, all in the new script:
1. `gen_ctxgas.py --selector` keeps only blocks 0 and 1 of the dispatcher checked. Selectors below
   0x3644e515 are compared in a second dispatcher block (index 3), which the guard proof then enters
   as unchecked and fails. The script checks every block that compares the function's selector
   (regenerates with `--skip` = the slice's skip list minus those).
2. `certify.py --segment 16` (transfer: 8). With 8, the inline-returns stage (evm10) is cut at the
   second dispatcher block; its cut relation keeps the selector as an unknown word, so the segment
   walks the excluded functions and the proof fails (seen for both). The script refuses any proof
   that cuts there.
3. transferFrom only: `--heartbeats 8000000`; its evm2 first segment timed out at 2000000.

Worth fixing upstream in solar's certify tooling: (1) and (2) are general for any function
dispatched past the first dispatcher block.

## Build receipts (hosted Hand, 5 cores, 14 GB, LEAN_NUM_THREADS=1, -KleanMemory=6000)

Each stage module built in its own `lake build` call; peak RSS of the process tree, wall time, exit code:

| Target | Modules | Peak RSS | Wall (sum) | Exit |
|---|---|---|---|---|
| uv2_erc20.ProofsA (Runs + Stages) | 17 | 1972 MB | 554 s | all 0 |
| uv2_erc20.ProofsTF (Runs + Stages) | 17 | 2559 MB (evm2) | 1206 s | all 0 |
| uv2_erc20.GasGuardA (guard N=5, sym_exec) + GasA | 2 | see next row | 21 s + 3 s | 0 |
| uv2_erc20.GasGuardTF + GasTF (guard N=11) | 2 | 3505 MB | 102 s | 0 |
| uv2_erc20.AnyCallerNested | 1 | 2822 MB | 493 s (with transfer's stages) | 0 |
| ContractsUniswapV2ERC20Nested with GasGuardA (one lake call) | all | 5900 MB | 440 s | 0 |
| Certified.Approve, Certified.TransferFrom | 2 | 2683 MB | 2.3 s, 2.6 s | 0 |

Final incremental build of all of the above: "Build completed successfully (2873 jobs)", exit 0.

`#print axioms` (also pinned by `#guard_msgs` in the modules): `Approve.certified`, `approve_bytes`,
`approve_keys_bytes`, `TransferFrom.certified`, `transferFrom_bytes`, `self_max_bytes`, `self_short_bytes`,
`CtxGasA.gas_edge`, `CtxGasTF.gas_edge`, `AnyCaller.Approve.backend_any_caller`,
`AnyCaller.TransferFrom.backend_any_caller`, `uv2_erc20_approve_mir_to_evmir`,
`uv2_erc20_transferFrom_mir_to_evmir`: [propext, Classical.choice, Quot.sound].
`rejects_sstore` (both): [propext, Quot.sound]. No sorry, admit or native_decide in the new or
generated files.

## Not done

- The source side (E3, E7) still fixes the caller at 0x2000, as for transfer.
- No concrete-storage self-transfer run on the bytes by `decide` (transfer has σmax/σshort): the
  transferFrom cases are stated for every storage under the scoped premise, which
  `HashScopeNested.transferFrom_scoped_witness` shows satisfiable.
- CI: the new modules need `uniswap_v2_stages_nested.sh` in the workflow that runs
  `uniswap_v2_stages.sh`; not added here.
