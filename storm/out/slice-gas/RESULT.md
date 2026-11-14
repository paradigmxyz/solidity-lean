# slice-gas (E8): UniswapV2ERC20.transfer gas bound on the exact runtime bytes

Base: solidity-lean `alpharush/certified-translation` 9fb89ee6; solar `alpharush/certified` 38b5232ad.
Deliverables: `sl-slice-gas.bundle` / `solidity-lean/0001-*.patch` (one commit, 27347975 on 9fb89ee6),
`solar-slice-gas.bundle` / `solar/0001-*.patch` (one commit, 41b240ef3 on 38b5232ad), `Audit.lean`.
Scope: UniswapV2ERC20.transfer only. Nothing GPL-derived is committed: the flattened port, the exported
stages and the certificate module are generated before the build (`scripts/verify/uniswap_v2_gas.sh`, git-ignored).

## What is proved (kernel-checked, axioms within propext, Classical.choice, Quot.sound)

Exact bytes: solar -Ogas --evm-version osaka of the generated port (source sha256 14da00cd...ac80b),
runtime 1183 bytes, sha256 ca4c1925...71a0b; `-Zemit-lean-stages` checked not to change them. Final EVM IR: `evm11`.

| Theorem | Statement (abridged) | Premises |
|---|---|---|
| `SolarTV.Export.UniswapV2ERC20.CtxGas.G_eq` | `G = gasBoundL cx.base 7 = 8199112` (22100 * 7 * 53 + 12) | none |
| `...CtxGas.check_ok` | `AssembleCtxGas.checkXL F (norm evm11) code cx = true` on the exact bytes | none (kernel evaluation) |
| `...CtxGas.guard_run`, `guard_ends` | every oracle, every call with selector 0xa9059cbb: `evm11` and the guarded program (21 non-transfer blocks replaced by self-jumps) end within 7 blocks with the same result | selector only |
| `...CtxGas.gas_edge` | **E8 edge**: for every caller a < 2^160, a != the contract, every oracle with CALLER = a and EthLib's Keccak-256, every transfer-selector call, every gas >= G: `Final.Target.runWithFrom a gas code call = some obs` and `evmirSem o` gives the same `obs` (success, output incl. revert data, logs, storage) | none beyond the binders; no premise mentions gas or EthLib's result |
| `...CtxGas.resources` | `Shapes.ResourcesFrom run code Valid (fun _ => G)` | `hv` (Valid within the transfer selector), `total` and `stage`: the source-to-`evm11` stage per caller under `oracleFrom a` (E3 then E4, other lanes) |
| `...CtxGas.resources_at` | `Shapes.Resources S p code Valid (fun _ => G)` (Verify/Shapes.lean, caller `callerAddress`) | as above, plus `run callerAddress = S.run p` |
| `AssembleCtxGas.forward_of_checkXLFrom` | generic: checkXL plus a run of `guard F p` within n blocks gives the bytes that result from any caller at gas >= gasBoundL | generic |
| `Shapes.gasEdge_ofXL`, `resourcesFrom_ofXL`, `ResourcesFrom.resources` | generic composition (Verify/ShapeCtxGasFrom.lean) | generic |

**EIP-2929 cold/warm**: the bound charges every item of the lowered program 22100 gas, at least the price of any
instruction the checker admits whatever the access set (cold SSTORE setting a zero slot 20000+2100, cold SLOAD 2100,
KECCAK256 of 64 bytes, LOG3 of 32 bytes). The theorem is about EthLib's own Fusaka interpreter, which meters the
accesses the run actually makes, so it holds for every warm/cold combination; no access-set model is assumed.
The bound is uniform and coarse (not tight). `G` is a constant below 2^64.

**Any caller**: `Final.Target.runWithFrom a gas` runs the message from account a (sender and origin, holding the call
value), with `runWithFrom_callerAddress : runWithFrom callerAddress = runWith`. The loop simulation (`exec_simL`,
`run_simXL`) now takes any caller (`OracleOkAt a`) and asks for `Target.txEnv` only when the program reads it
(transfer's slice does not: `reads = false`). Excluded: a = selfAddress (the contract calling itself).

**Call-free route**: checkXL is the loop checker's fragment (no STATICCALL/CALL/GAS in checked blocks); no
`StaticRunner`/`CalleesRun` hypothesis anywhere (consistent with AssembleNoCall's refutation of StaticRunner).

## Negative controls (by execution in the kernel)
- `rejects_jump`: checkXL refuses the bytes with byte 7 (the dispatcher's first jump target) changed.
- `rejects_sstore`: checkXL refuses the bytes with transfer's debit SSTORE (byte 0x427) replaced by POP.
- The guard stage fails closed: `sym_exec` leaves a goal if any transfer path reaches a guarded block.

## Build receipts (hosted Hand, 14 GB, LEAN_NUM_THREADS=1, -KleanMemory=6000, Lean v4.35.0)
Generation: `scripts/verify/uniswap_v2_gen.sh && SOLAR_DIR=<solar wip> scripts/verify/uniswap_v2_gas.sh`: exit 0.
Clean rebuild of the new modules (their oleans deleted first):
`lake build -KleanMemory=6000 SolidCore.Refinement.Solar.AssembleCtxGas SolidCore.Refinement.Solar.AssembleCtxGasFrom Verify.ShapeCtxGas Verify.ShapeCtxGasFrom uv2_erc20`: **exit 0**, 78 s, "Build completed successfully (2778 jobs)".
Then Gas.lean rebuilt after moving its negatives onto the walk (`lake build -KleanMemory=6000 uv2_erc20`): **exit 0**.

| Module | time | peak RSS (MB, incl. mmapped imports) |
|---|---|---|
| SolidCore/Refinement/Solar/AssembleCtxGas.lean | 3.2 s | 2249 |
| SolidCore/Refinement/Solar/AssembleCtxGasFrom.lean | 2.3 s | 2177 |
| Verify/ShapeCtxGas.lean | 2.1 s | 2270 |
| Verify/ShapeCtxGasFrom.lean | 2.2 s | 1781 |
| Certified/uv2_erc20/CtxGas.lean (generated) | 5.9 s | 2677 |
| Certified/uv2_erc20/GasGuard.lean | 31 s | 2908 |
| Certified/uv2_erc20/Gas.lean | 3.3 s | 2777 |

The modified AssembleLoop/AssembleLoopSim/AssembleLoopRun/AssembleRunLoop and their dependents
(AssembleGasLoop, AssembleCtxCall, AssembleRevertCall) built with exit 0 in the earlier full build of this lane.
Axiom audit (`lake env lean -M 6000 Audit.lean`, exit 0), verbatim:

```
'SolarTV.Export.UniswapV2ERC20.CtxGas.gas_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.resources_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.G_eq' does not depend on any axioms
'SolarTV.Export.UniswapV2ERC20.CtxGas.check_ok' depends on axioms: [propext, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.guard_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.guard_ends' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.rejects_jump' depends on axioms: [propext, Quot.sound]
'SolarTV.Export.UniswapV2ERC20.CtxGas.rejects_sstore' depends on axioms: [propext, Quot.sound]
'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXLFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Refinement.Solar.AssembleCtxGas.forward_of_checkXL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'SolidCore.Refinement.Solar.AssembleCtxGas.within_of_checkXL' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Refinement.Shapes.gasEdge_ofXL' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Refinement.Shapes.resourcesFrom_ofXL' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Refinement.Shapes.ResourcesFrom.resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Refinement.Shapes.compiled0XL' depends on axioms: [propext, Classical.choice, Quot.sound]
'SolidCore.Refinement.Final.Target.runWithFrom_callerAddress' depends on axioms: [propext, Classical.choice, Quot.sound]
gas_edge : ∀ a < 2 ^ 160,
  a ≠ SolidCore.Refinement.selfAddress →
    ∀ (o : SolarTV.Machine.Oracle),
      SolidCore.Refinement.Solar.AssembleLoop.OracleOkAt a o →
        ∀ (call : SolarTV.Call),
          TransferCall call →
            ∀ (gas : ℕ),
              G ≤ gas →
                ∃ obs,
                  (SolarTV.evmirSem o).run prog call = some obs ∧
                    SolidCore.Refinement.Final.Target.runWithFrom a gas code call = some obs
@resources : ∀ {Valid : SolarTV.Call → Prop} {run : ℕ → SolarTV.Call → Option SolarTV.Observable},
  (∀ (call : SolarTV.Call), Valid call → TransferCall call) →
    (∀ a < 2 ^ 160,
        a ≠ SolidCore.Refinement.selfAddress → ∀ (call : SolarTV.Call), Valid call → ∃ obs, run a call = some obs) →
      (∀ a < 2 ^ 160,
          a ≠ SolidCore.Refinement.selfAddress →
            ∀ (call : SolarTV.Call),
              Valid call →
                ∀ (obs : SolarTV.Observable),
                  run a call = some obs →
                    (SolarTV.evmirSem (SolidCore.Refinement.Shapes.oracleFrom a)).run prog call = some obs) →
        SolidCore.Refinement.Shapes.ResourcesFrom run code Valid fun x => G
def SolidCore.Refinement.Shapes.ResourcesFrom : (ℕ → SolarTV.Call → Option SolarTV.Observable) →
  ByteArray → (SolarTV.Call → Prop) → (SolarTV.Call → ℕ) → Prop :=
fun run code Valid G =>
  ∀ a < 2 ^ 160,
    a ≠ SolidCore.Refinement.selfAddress →
      ∀ (call : SolarTV.Call),
        Valid call →
          G call < 2 ^ 64 ∧
            ∀ (gas : ℕ),
              G call ≤ gas → gas < 2 ^ 256 → SolidCore.Refinement.Final.Target.runWithFrom a gas code call = run a call
```
No `sorry`, `native_decide`, `admit` or `axiom` in the new files.

## Not proved here (blocks CERTIFIED; named)
- `stage`/`total` of `resources`: SolidCore's transfer from any caller to `evm11` under `oracleFrom a` (E3 source to MIR,
  E4 backend stages). A source run from any caller (`Source.runFrom`) is on `ck5/any-caller`, not in 9fb89ee.
- `Shapes.Resources` in Verify/Shapes.lean is caller-fixed; the final statement should use `Shapes.ResourcesFrom`.
- E6 binding: `code` is the exporter's `Bytecode.lean` of this run; the driver's byte equality is lane slice-final's.
- Tightness of G; a concrete out-of-gas run below G is not shown.
- Credits: AssembleCtxGas.lean, ShapeCtxGas.lean, asm_ctx.py, gen_ctx.py, gen_ctxgas.py start from lane slice-final's
  pre-reset work; this lane fixed and exercised them (any caller, norm, slicing, Lean layout).
