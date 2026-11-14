# slice-stages: UniswapV2ERC20.transfer's backend stages from any caller

Base: solidity-lean #166 head d0ab5d6 (alpharush/certified-translation). Solar: #2637 head 697fc686
(paradigmxyz/solar, on GitHub). Patch: `any-caller.patch`, bundle `any-caller.bundle` (d0ab5d6..d0ab5d6+1, one commit).

## Finding: E4 was never fixed to 0x2000; the pin is in E3 and the composition

`uv2_erc20_transfer_mir_to_evmir (o : Oracle) : Stage (mirSem o) (evmirSem o) stage0 evm11 scope` holds under
every oracle, and the machine reads CALLER from `Oracle.caller` (`tv/SolarTV/Machine.lean`: `.caller => o.caller`).
The generated stage proofs (solar 697fc686's certify.py) contain no `0x2000`, `8192`, `callerWord` or `CallerOk`,
and they execute CALLER (5 sites in evm11, 3 in stage0) as an unknown word. The only caller pins are
upstream: E3's `SourceEnvOk` (`CallerOk o`), and `Slice/Post`'s `caller := callerWord`. This lane now states
E4, and E4∘E5, for any caller, plus the exact hypothesis that slice-source-mir's symbolic-caller E3 has to provide.

## Theorems (new `Certified/uv2_erc20/AnyCaller.lean`, namespace `SolarTV.Export.UniswapV2ERC20.AnyCaller`, a root of lib `uv2_erc20`)

```lean
theorem stages_from (a : Nat) :
    Stage (mirSem (oracleFrom a)) (evmirSem (oracleFrom a)) stage0 evm11 scope

theorem backend_any_caller : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ o, AssembleLoop.OracleOkAt a o →
    ∀ call, TransferCall call → ∀ obs, (mirSem o).run stage0 call = some obs →
      ∀ gas, G ≤ gas → Final.Target.runWithFrom a gas code call = some obs      -- G = 8199112

theorem resources_any_caller {Valid run}
    (hv : ∀ call, Valid call → TransferCall call)
    (total : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∃ obs, run a call = some obs)
    (source : ∀ a, a < 2 ^ 160 → a ≠ selfAddress → ∀ call, Valid call → ∀ obs, run a call = some obs →
      (mirSem (oracleFrom a)).run stage0 call = some obs) :
    ResourcesFrom run code Valid (fun _ => G)

theorem any_caller_inhabited :
    ∃ a o, a ≠ callerAddress ∧ a < 2 ^ 160 ∧ a ≠ selfAddress ∧ AssembleLoop.OracleOkAt a o   -- a = 0x3000
```

`backend_any_caller` takes the first lowered MIR on a transfer call down to EthLib's run of the exact runtime bytes,
from every caller a, under every oracle whose CALLER is a and whose Keccak-256 is EthLib's. It combines E4 (`transfer_scope`:
a transfer selector is in E4's scope) with E5 `gas_edge`. `resources_any_caller` is the integration point: once E3 holds
per caller into `stage0` under `oracleFrom a` (the `source` hypothesis), the whole chain gives `ResourcesFrom` (any caller).
Each theorem's `#print axioms` is pinned with `#guard_msgs` to [propext, Classical.choice, Quot.sound].

## Build receipts (hosted Linux, Lean v4.35.0, LEAN_NUM_THREADS=2; peak = largest single process RSS)

| command | exit | wall | peak |
|---|---|---|---|
| `scripts/verify/uniswap_v2_gen.sh` | 0 | 1 s | 30 MB |
| `SOLAR_DIR=<solar 697fc686, release> scripts/verify/uniswap_v2_stages.sh` | 0 | <1 s | 21 MB |
| `lake -R build -KleanMemory=6000 uv2_erc20` (fresh generation, 2813 jobs, AnyCaller included) | 0 | 333 s | 4711 MB (uv2_erc20.Ctx 4.82 GB; CtxNeg 3.27 GB; per-lean VmHWM sampling) |
| caller-hardcoding negative control (below), `lake build -KleanMemory=6000 uv2_erc20.ProofsT.Runs.Evm11` | **1** | 21 s | 1881 MB |
| `lake -R build -KleanMemory=6000 uv2_erc20` after restoring | 0 | 29 s | 1867 MB |

Scan of Certified/uv2_erc20 (generated and new): no `sorry`, `native_decide`, `bv_decide`, `axiom`, `implemented_by`.
Logs: `build.log`, `neg_caller.log`, `rebuild.log`, `gen.log`.

## Negative control: a stage that is right only for caller 0x2000 is refused

All 5 `.effect .caller 0` in `evm11` were replaced by `.op (.stack (.push 0x2000))`. The result is correct for caller 0x2000 and
wrong for every other caller, so a fixed-caller proof could accept it. Rebuilding the last pass's proof failed by execution:
`sym_seg: the segments end differently on this path` (Runs/Evm11.lean:67), so `evm11_certified`/`_back` fall back to
`sorryAx` and their `#guard_msgs` axiom pins fail. No timeout. After restoring the file, the build exits 0.

## Changes (one commit, `feat(uv2_erc20): transfer backend stages from any caller`)

- `Certified/uv2_erc20/AnyCaller.lean` (new, committed: contains no GPL-derived text) and lakefile root `uv2_erc20.AnyCaller`.
  CI's existing `lake build -KleanMemory=6000 uv2_erc20 …` steps build it.
- `scripts/verify/uniswap_v2_stages-solar-rev`: 6edf8f40 → 697fc6864620d2fdb0b9b3ff66882ae4ad56b41e (#2637 head, fetchable
  from GitHub). The previous lane's local-only pin problem is gone.

## Not claimed

- **E3 for any caller is not proved here.** That is slice-source-mir's work. `source` in `resources_any_caller` is what it has to supply.
  Until it lands, the end-to-end chain from source is caller 0x2000.
- E7's `TargetPost` still names `caller := callerWord`. Generalizing the post to any caller is outside the backend stages.
- Scope is transfer's selector only. Other functions are excluded from E4.
