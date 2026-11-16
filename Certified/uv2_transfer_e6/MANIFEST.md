# UniswapV2ERC20.transfer from every caller: artifact manifest

The claim is `Certified.uv2_transfer_e6.Final.final : Statement` (Statement.lean). It is two
instances of `SolidCore.Verify.Generic.Expected` over the 1183 runtime bytes that solar emitted for
the flattened port. Both instances take the caller as a parameter (`Context.Ok`: below `2^160`, not
the contract):

* `specAny`: every real caller and every well-formed `transfer(to, v)` without value. The
  postcondition is the caller-aware sequenced updates (`SeqPostAt`) unconditionally, and the
  caller-aware property `TargetPostAt` wherever the call's finite footprint is Keccak-separated.
* `specScoped`: every real caller whose own footprint is separated. Each valid call carries the
  finite-footprint premise `ScopeAt` (`ScopedSep (transferFootprint 1 caller to)`), and the
  postcondition is `TargetPostAt`.

`TargetPostAt` decides overflow (`s[to] + v < 2^256`) and the self-transfer (succeeds iff
`s[a] >= v` and changes no storage); neither is assumed. Both instances certify equivalence at
every gas, termination with an allowed status, and resources: from 8199112 gas on, the bytes'
observable equals the source's. That is observable equality, not a no-out-of-gas claim. Both are
unconditional (`assumptions = []`) and runtime-tier: the constructor and init code, the lifecycle
and reentrancy are out. The contract's address, block and transaction are `Target.message`'s.

## Pins

| Item | Pin |
|---|---|
| solidity-lean base | 4332b47d3495790581a8d0d4f18f690bd8f3d5a6 (= 44572c15 + the transfer lane's `TransferExpected.lean`) |
| Lean | `leanprover/lean4:v4.35.0`; `lean` sha256 bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38, `leanchecker` sha256 12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6 |
| Compiler (stages and fresh bytes) | paradigmxyz/solar 697fc6864620d2fdb0b9b3ff66882ae4ad56b41e (`scripts/verify/uniswap_v2_stages-solar-rev`), release binary sha256 dca17546509f702c38639487a73c101b72d97718f0e13d51c307d1b971b92851 (this build) |
| Options | `-Ogas --evm-version osaka` (`Certified/uv2_erc20/options`, sha256 e8dcb59d…038c) |
| Spec exporter | solar-verify from solar 902cccc2cb1213219789780a39caf3c1d4d9f35e, binary sha256 4468c71522c1e26e15e20808b87f5d4e0e81070602fce1ed2eea02c262cbd464 |
| Port | solar 67946d7d204862c9d28ed18b83604aa00546f5f6 `solar-tv/uniswap-v2/port.py` over Uniswap/v2-core 6a9e7c97860676e0992f22a49665760444c1cdf5; flattened `scripts/verify/uniswap-v2/UniswapV2ERC20.sol` sha256 14da00cdeaf2ab3709d2d9838be2c2a144502b32b874b55394d7a8792deac80b |
| Frontend | solc 0.8.35+commit.47b9dedd (`.cache/solc-0.8.35`, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4) |
| Importer | `scripts/solc_ast_to_lean_source.py` (sha256 5b35afb6…2e3b) via `scripts/verify/uniswap_v2_sources.py` (sha256 9b9a3f65…e03e) → `Contracts/UniswapV2/ERC20/Source.lean` (sha256 e7f4cd9c…bfbc) |
| Checkers | solar c09510a39b5c9940845d2c19928c742f676b8675 `tools/certify/check_final.lean` (sha256 6cc14892…7f3a), `tools/certify/replay.py` (sha256 361ae120…82a2) |

Trusted computing base: Lean's kernel (`leanchecker` replay), solc's frontend and the importer
(the source is SolidCore's reading of solc's AST), the port (the flattened file is what is
certified, not v2-core as written), the specification's text in Statement.lean, and EthLib's EVM
model.

## Files

| sha256 | Path | Role |
|---|---|---|
| 80b4640f5079914a1f712e8a307b2f54f41b546ab0dea47d98d05b930ea617c5 | Certified/uv2_transfer_e6/Statement.lean | statement, fresh bytes (imports no proof) |
| f591aa16c02f2b6bb2bc0834d9ba5f16a56732755cfc4b394ee65616a0240e10 | Certified/uv2_transfer_e6/Proof.lean | proof (untrusted) |
| 1678cc546eda700e7f0c820fce6a44db0e70d764586cc4f9e4282ff9aae98216 | Certified/uv2_transfer_e6/Final.lean | `final : Statement` |
| bc6f385ff2ba77985c3a95b4bc60989806da785b05571ddd50f2b759be4de7f7 | Certified/uv2_transfer_e6/verify_bytes.sh | re-emit and compare |
| e9861faadf9c09cbd4a4dda8361be284cd01c0fb765c0bfffad534276de08605 | Contracts/UniswapV2/ERC20/Slice/Post.lean | definitions the statement reads (generated) |
| 8573c6944c24c3d578aaf1f52f127de5053c8e461318dfb3ba71c8fc767c988c | Contracts/UniswapV2/ERC20/Certified/TransferExpected.lean | dependency (base) |
| 169c839bf7e2a3b25ccaa61615a6a5f5ee1fc24c2c88e812a75397644ee40d9c | Contracts/UniswapV2/ERC20/Certified/TransferFrom.lean | dependency (base) |
| 0713bf83bc8ef071e64931f2a7811822f6f2ed82d8989886d5b840394f7b4843 | Certified/uv2_erc20/CtxGas.lean | exported code (generated) |

Generated inputs (not committed, GPL-3.0 port): `scripts/verify/uniswap_v2_gen.sh`,
`uniswap_v2_stages.sh`, `uniswap_v2_transfer_slice.sh` at the pins above.

## Commands and receipts

```sh
scripts/verify/uniswap_v2_gen.sh && scripts/verify/uniswap_v2_stages.sh            # exit 0
lake build -KleanMemory=6000 Contracts.UniswapV2.ERC20.Core                          # exit 0
SOLAR_DIR=<solar 902cccc2> SOLAR_VERIFY=<it>/target/release/solar-verify \
  scripts/verify/uniswap_v2_transfer_slice.sh                                       # exit 0
LEAN_NUM_THREADS=1 lake -R build -KleanMemory=6000 uv2_transfer_e6                  # exit 0, "Build completed successfully (2842 jobs)"
bash Certified/uv2_transfer_e6/verify_bytes.sh                                      # exit 0, "fresh 1183 bytes, statement 1183 bytes, equal True"
lake env lean --run check_final.lean uv2_transfer_e6 uv2_transfer_e6.Proof          # exit 0
```

`check_final`: `Certified.uv2_transfer_e6.Final.final : Certified.uv2_transfer_e6.Final.Statement`
(module `uv2_transfer_e6.Statement`, which does not import `uv2_transfer_e6.Proof`); axioms
`[propext, Classical.choice, Quot.sound]`. The kernel checks the binding in `Proof.bound`
(`decide +kernel`: the exported code's bytes are `runtimeBytes`), and `verify_bytes.sh` checks that
`runtimeBytes` is what the pinned solar emits.

Closure replay: `replay.py plan --include-trusted` gives 4027 modules, 4027 to replay, 0 trusted;
`leanchecker --verbose` over all of them, then `replay.py account`. Result: REPLAY_RESULT.

## Negatives (each exits nonzero)

| Case | Command | Exit |
|---|---|---|
| Statement bytes with byte 0 changed (0x60→0x61) | `verify_bytes.sh` on the mutated Statement.lean | 1 (`equal False`) |
| Kernel binding to mutated bytes | `decide +kernel` of `code bytes = 0x61 :: runtimeBytes.tail` | 1 (kernel proves it false) |
| Postcondition fixed to caller 0x2000 in every context | `Expected src specMut runtimeBytes := certAny.expected` | 1 |
| Self-transfer also requiring no overflow | same harness on `specScoped` | 1 |
| Contract's own address admitted as caller | same harness | 1 |
| Gas bound 8199111 | same harness | 1 |
| Source names another contract (`IUniswapV2ERC20`) | same harness | 1 |
| Recipient credited `v + 1` | same harness, through `meets` and `omega` | 1 |
| Unmutated control | same harness, published statement | 0 |

Only the two byte cases are refutations. The five harness cases show the proof does not certify
the mutated statement; they are not proofs that the mutated statements are false.
