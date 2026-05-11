# Forge/Lean EVM Parity Harness

This harness runs raw EVM bytecode through Foundry's EVM and the Lean Osaka
interpreter, then compares success/revert status, returndata, gas used, gas
remaining, refunds, selected storage slots, selected account state, and logs.
It supports preinstalled multi-contract worlds by passing additional account
runtime bytecode and account storage to the Lean CLI.

Run it from the repository root:

```sh
python3 tests/bin/evm_parity.py forge
```

The broader upstream-suite work is tracked by `foundry-suites.toml` and
`UPSTREAM_SUITES.md`. The corpus helper can list, fetch, scan, and run pinned
Foundry repositories while the Lean replay runner grows:

```sh
python3 tests/bin/foundry_corpus.py list
python3 tests/bin/foundry_corpus.py scan --suite local-forge-parity
```

The Forge tests live in `test/EvmParity.t.sol`. Each case installs raw runtime
bytecode with `vm.etch`, executes it with a fixed gas limit, reads Foundry's
callee-perspective `vm.lastCallGas()`, and calls `tests/bin/evm_parity.py check`
through FFI. The checker runs `.lake/build/bin/evm_parity` when available, or
falls back to `lake exe evm_parity`.

Useful case knobs exposed by the Lean CLI:

- `--code`, `--calldata`, `--gas`, `--fuel`
- `--call-depth`
- `--address`, `--caller`, `--origin`, `--coinbase`
- `--timestamp`, `--number`, `--gaslimit`, `--basefee`, `--chainid`
- `--balance`, `--callvalue`
- `--nonce`
- repeated `--account address=code`
- repeated `--account-balance address=value`
- repeated `--account-nonce address=value`
- repeated `--account-storage address:key=value`
- repeated `--account-original-storage address:key=value`
- repeated `--storage key=value`
- repeated `--original-storage key=value`
- repeated `--keccak bytes=word`
- repeated `--warm-address address`
- repeated `--warm-storage key`

Current cases cover return, revert, `GAS`, cold `SLOAD`, cold `SSTORE`,
storage-state comparison, `LOG1`, and `SELFBALANCE`. They also include a
compiled Solidity contract with a real dispatcher, public storage getters,
nested branches, `for`/`while` loops, fixed memory arrays, dynamic `bytes`
calldata, storage mutation, an indexed event, and a custom-error revert. The
multi-contract cases install separate caller, worker, and delegate library
runtimes and cover `CALL`, `STATICCALL`, caught child reverts, `DELEGATECALL`,
value transfer, cross-account storage, account balances, and emitted logs.
Dynamic deployment cases now cover `CREATE` and `CREATE2` by passing the
needed address-derivation Keccak preimages into Lean's hash oracle, checking the
factory's stored deployed address/result, the created contract's storage,
balance and nonce, constructor/runtime/factory logs, and gas.

The stateful replay runner also intercepts the Foundry cheatcode address in
Lean. The current alpha tier covers state mutation and inspection (`deal`,
`etch`, `store`, `load`, nonces), caller control (`prank`, `startPrank`,
`stopPrank`), block/env setters, access-list warm/cool helpers, log recording,
snapshots, and host-oracled `addr`/`sign` results. `expectEmit`, `expectCall`, and `label` are accepted as
permissive no-ops until assertion semantics are modeled.
