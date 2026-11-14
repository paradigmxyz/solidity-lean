# slice-final: UniswapV2ERC20.transfer

**Status: proved in Lean as `Shapes.Certified` (equivalence, termination with allowed statuses,
the sequential post, resources) for `transfer(address,uint256)` on the exact 1183-byte runtime,
for calls from the framework's caller 0x2000.** This is narrower than docs/CERTIFICATION_TARGET.md
in one named way: the target's Valid admits any caller, and the Lean framework's `Call` has no
caller field (`Generic.callerWord = 0x2000`). Any caller is covered by executed tests only (below).
The certify driver's rule also reports `strongest = false`, because the post is slice-final's Lean
restatement, not a solar-verify export. Nothing here claims more than that.

Scope is UniswapV2ERC20.transfer only; every other selector is outside Valid.

## The statement (as final.py wrote it, checked by check_final.lean)

```lean
def Statement : Prop :=
  code.data.toList.map (·.toNat) = runtimeBytes ∧
    NonVacuous ∧
    (∃ c, SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c ∧
      Shapes.Certified (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) c code
        Transfer.Valid Transfer.Allowed Transfer.Post (fun _ => 6401574412))
```

`runtimeBytes` is the bytecode of a fresh compile of the pinned source by solar 38b5232 (sha256 of
the source 3b4e2e90…, byte-identical to the export), written out as numbers and decided by the
kernel. `NonVacuous`: a valid call whose revert the post rejects, and a revert without the source's
data that Allowed rejects. No premises (`env = []`).

Inputs (Contracts/UniswapV2/ERC20/Transfer/Spec.lean, namespace
`SolidCore.Spec.UniswapV2.ERC20.Transfer`; slice-final's own Post, pending slice-spec's names):

* **Valid**: `∃ σ dst v, Covers deployed σ ∧ dst < 2^160 ∧ v < 2^256 ∧ call = {calldata :=
  Abi.calldata 0xa9059cbb [dst, v], callvalue := 0, storage := σ}`: well-formed calldata, no value,
  any storage that names the constructor's slot 3, caller 0x2000.
* **Post** (sequential, over physical slots): with `S := slotValue storage`, `balSlot a =
  keccak(a, 1)`, `debited σ v` (caller's slot minus v), `credited σ' dst v` (recipient's slot of
  σ' plus v), `Succeeds σ dst v := v ≤ σ(balSlot C) ∧ debited σ v (balSlot dst) + v < 2^256`:
  * success: `success = true`, output the word 1, logs exactly `[([Transfer topic, C, dst], word v)]`,
    and `∀ n < 2^256, storage n = credited (debited S v) dst v n` (frame over every physical slot:
    only the caller's and recipient's slots change);
  * otherwise: `success = false`, no logs, storage unchanged, output
    `Error("ds-math-sub-underflow")` when `S(balSlot C) < v`, else `Error("ds-math-add-overflow")`.
  * dst = C: the credit reads the debited slot, so there is no recipient overflow and the balance is
    unchanged (`self_max_succeeds`); balance < v reverts with sub-underflow (`self_insufficient`).
* **Allowed**: success, or exactly those two reverts under their conditions.
* **PostKeys** (not part of the statement): the same per key under the footprint-scoped premise
  `ScopedSep (transferFootprint 1 C dst)` (Verify/Spec/HashScope.lean). The certified Post speaks of
  slots, so the statement needs no hash premise at all; `exists_separatedBy` (abstract model) and
  the real-keccak witness `scopedSep_transfer_example` are not used by it.

## Edges

| Edge | Status | Where |
|---|---|---|
| Source → first lowered MIR (E3) | proved, kernel evaluation | Transfer/Source.lean `check_ok`, `deploy_eq` |
| MIR stages stage0 → evm11 (E4) | proved, transfer scope | uv2_erc20.ProofsT (generated), `uv2_erc20_t_mir_to_evmir` |
| Guard stage (permit's blocks 21, 29 unreachable on Valid) | proved | uv2_erc20.GuardT `guard_run`, `guard_ends` |
| evm11 → exact bytes, with gas (E5+E8) | proved by `checkXL` (kernel), no runner premises | uv2_erc20.CtxGas `check_ok`; Verify/ShapeCtxGas.lean `compiled_ofXL` |
| Compiled shape on Valid | proved | Transfer/Compiled.lean `compiled_valid` |
| Erased tree = SolidCore's | proved (kernel_rfl) | Transfer/Certified.lean `shape_eq` |
| Tree meets Post / Allowed | proved | Transfer/Tree.lean `tree_post`; Certified.lean `meets`, `allowed` |
| Certified + published statement | proved; check_final passes | `certified`, `certified_lit`, `Certified.uv2_erc20.Final.final` |
| Any caller | **missing** (framework fixes 0x2000) | executed: `testFuzz_post` over arbitrary callers |
| Post bound to a solar-verify export | **missing** (Lean restatement) | driver reports strongest = false |
| leanchecker replay of the closure | **not run** | check_final listed 4000 modules for replay |

StaticRunner stays refuted (`AssembleNoCall.not_forall_staticRunner`) and UV2's bytes are not
call-free (permit's STATICCALL); the checkXL route needs neither. The gas bound is the checker's
coarse bound (6,401,574,412).

All theorems: `#print axioms` is `[propext, Classical.choice, Quot.sound]` (checked with
`#guard_msgs` in the files and by check_final for `final`). No sorry, admit or native_decide in
the new files.

## Negatives

Kernel (Transfer/Neg.lean, `decide +kernel`, same final EVM IR and certificate):
`missing_debit`: checkXL = false with SWAP1 SSTORE at 0x426 replaced by POP POP;
`altered_jump`: checkXL = false with the PUSH2 target at 0x438 changed from 0x0466 to 0x0405
(sites checked by `missing_debit_sites`, `altered_jump_sites`).

Executed (forge/test/TransferSlice.t.sol on the exact runtime bytes, EVM osaka, 2000 fuzz runs;
`RUNTIME_HEX=runtime.hex forge test`, exit 0, 8/8 pass):
`test_selfTransferMaxBalance` (balance 2^256-1, v=1, caller = to: succeeds, unchanged, Transfer log),
`test_selfTransferInsufficient` (reverts, sub-underflow data, no change), `test_distinct`
(incl. recipient overflow and underflow), `testFuzz_post` (any caller, self or distinct, the
sequential post incl. revert data), `test_envValueRejected` (callvalue 1 → empty revert),
`test_neg_missingDebit`, `test_neg_alteredJump`, `test_neg_wrongPost` (the non-sequential post
predicts a revert on the 2^256-1 self-transfer; the bytes succeed). Env mismatch:
`forge test --evm-version paris --match-test test_selfTransferMaxBalance` fails (exit 1; PUSH0).
runtime.hex is not committed (compile the pinned source to regenerate).

## Build receipts (Lean 4.35.0, 5 cores, 14 GB; `~/peak.py` = exit, wall, peak RSS of a child)

| Run | Command | Exit | Wall | Peak |
|---|---|---|---|---|
| b7 | `lake build -KleanMemory=6000 Contracts.UniswapV2.ERC20.Core Contracts.UniswapV2.ERC20.SpecTreeKeccak Verify.VC.KernelIdx` | 0 | 126 s | 3122 MB |
| b10 | `lake build -KleanMemory=9000 SolidCore.Refinement.Solar.AssembleCtxGas Verify.ShapeCtxGas Verify.Spec.TreeOn uv2_erc20.CtxGas uv2_erc20.GuardT Contracts.UniswapV2.ERC20.Transfer.Certified` (oleans of these removed first) | 0 | 300 s | 13520 MB |
| b10b | same Certified after adding nonvacuous, certified_lit | 0 | 41 s | 5353 MB |
| b11 | `lake build -KleanMemory=9000 Contracts.UniswapV2.ERC20.Transfer.Neg` | 0 | 62 s | 6310 MB |
| b12 | `lake build -KleanMemory=9000 uv2_erc20.Statement uv2_erc20.Final` | 0 | 10 s | 2675 MB |
| check | `lake env lean --run tools/certify/check_final.lean uv2_erc20 Contracts.UniswapV2.ERC20.Transfer.Certified` | 0 | 15 s | 7973 MB |

The CtxGas certificate is the memory peak (about 13.5 GB): build it alone on a 16 GB machine.

## Reproduce

1. solidity-lean: base 9fb89ee, apply `solidity-lean.bundle` (branch slice-final3, head ff69626) or
   the patches in solidity-lean/. solar: base 38b5232, `solar.bundle` (head 3f1ecf8) or solar/.
2. Generate the GPL-derived inputs (not committed): `scripts/verify/uniswap_v2_gen.sh` (Core), the
   export of Certified/uv2_erc20/uv2_erc20.sol into Certified/uv2_erc20/gen, the stage proofs with
   `tools/certify/certify.py … --proof-dir Certified/uv2_erc20/ProofsT --proof-module uv2_erc20.ProofsT
   --namespace SolarTV.Milestone.Uv2Erc20T --label uv2_erc20_t` (transfer only, other selectors
   excluded), then `gen_ctxgas.py` (CtxGas.lean, `--skip 21,29`) and `gen_guard.py` (GuardT.lean).
3. `final.py shape_transfer.json --name uv2_erc20 --contract UniswapV2ERC20 --hex <runtime>`, build
   b10–b12, run check_final.
