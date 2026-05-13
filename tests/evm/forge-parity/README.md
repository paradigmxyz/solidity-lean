# Forge/Lean EVM Parity Harness

This harness runs raw EVM bytecode through Foundry's EVM and the Lean Osaka
interpreter, then compares success/revert status, returndata, gas used, gas
remaining, refunds, selected storage slots, selected account state, and logs.
It supports preinstalled multi-contract worlds by passing additional account
runtime bytecode and account storage to the Lean CLI.

The CLI invokes `SolidCoreYulCore.BytecodeMultiContract.runTransaction`
directly to keep the test executable small. Public L07 exposes the same runner
through `L07_MeteredEvm.runMetered`. L06 is the proof-facing shared
`External`-oracle boundary, and P06 proves the L05 bytecode artifact equivalent
to that L06 boundary before any exact metered-runner claim. Raw child frames
still use `runFuel` internally; `runTransaction` adds transaction-boundary
cleanup such as clearing transient storage and finalizing destroyed account
views.

Run it from the repository root:

```sh
python3 tests/bin/evm_parity.py forge
```

The broader upstream-suite work is tracked by `foundry-suites.toml`. The corpus
helper can list, fetch, scan, and run pinned Foundry repositories while the Lean
replay runner grows:

```sh
python3 tests/bin/foundry_corpus.py list
python3 tests/bin/foundry_corpus.py scan --suite local-forge-parity
```

The Forge tests live in `test/*.t.sol`: `EvmParity.t.sol` carries the broad
suite, and focused files keep newer edge cases from bloating that contract.
Each case installs raw runtime bytecode with `vm.etch`, executes it with a fixed
gas limit, reads Foundry's callee-perspective `vm.lastCallGas()`, and calls
`tests/bin/evm_parity.py check` through FFI. The checker runs
`.lake/build/bin/evm_parity` when available, or falls back to
`lake exe evm_parity`.
The Forge side passes `lastCallGas().gasLimit` and the observed block fields
into Lean rather than relying on nominal request/default values, so
value-transfer stipend effects and block-context opcode reads are part of the
replayed callee environment.
The `--fuel` and `--call-depth` knobs are Lean execution bounds used to keep the
runner total. They are not evidence for the EVM's 1024-frame call-depth rule;
parity cases stay below these bounds, and public target claims must assume the
configured bounds are sufficient for the compared execution.

Useful case knobs exposed by the Lean CLI:

- `--code`, `--calldata`, `--gas`, `--fuel`
- `--call-depth`
- `--address`, `--caller`, `--origin`, `--gasprice`, `--coinbase`
- `--timestamp`, `--number`, `--prevrandao`, `--block-gas-limit`, `--basefee`,
  `--blobbasefee`, `--chainid`
- repeated `--blockhash number=hash`
- repeated `--blobhash hash`
- `--balance`, `--callvalue`
- `--nonce`
- repeated `--account address=code`
- repeated `--account-balance address=value`
- repeated `--account-nonce address=value`
- repeated `--account-storage address:key=value`
- repeated `--account-original-storage address:key=value`
- repeated `--expect-account-code address=code`
- repeated `--expect-account-codesize address=size`
- repeated `--expect-account-codehash address=word`
- repeated `--storage key=value`
- repeated `--original-storage key=value`
- repeated `--expect-transient-storage key=value`
- repeated `--expect-account-transient-storage address:key=value`
- repeated `--keccak bytes=word`
- repeated `--sha256 bytes=word`
- repeated `--ripemd160 bytes=word`
- repeated `--modexp bytes=bytes`
- repeated `--blake2f bytes=bytes`
- repeated `--ecadd bytes=bytes`
- repeated `--ecmul bytes=bytes`
- repeated `--ecpairing bytes=bytes`
- repeated `--ecadd-fail bytes`
- repeated `--ecmul-fail bytes`
- repeated `--ecpairing-fail bytes`
- repeated `--point-evaluation bytes`
- repeated `--point-evaluation-fail bytes`
- repeated `--p256-verify bytes`
- repeated `--p256-verify-fail bytes`
- repeated `--bls-g1add bytes=bytes`
- repeated `--bls-g1msm bytes=bytes`
- repeated `--bls-g2add bytes=bytes`
- repeated `--bls-g2msm bytes=bytes`
- repeated `--bls-pairing bytes=bytes`
- repeated `--bls-map-fp-to-g1 bytes=bytes`
- repeated `--bls-map-fp2-to-g2 bytes=bytes`
- repeated `--bls-g1add-fail bytes`
- repeated `--bls-g1msm-fail bytes`
- repeated `--bls-g2add-fail bytes`
- repeated `--bls-g2msm-fail bytes`
- repeated `--bls-pairing-fail bytes`
- repeated `--bls-map-fp-to-g1-fail bytes`
- repeated `--bls-map-fp2-to-g2-fail bytes`
- repeated `--cheat-addr privateKey=address`
- repeated `--cheat-sign privateKey:digest=v:r:s`
- repeated `--warm-address address`
- repeated `--warm-storage key`

Current cases cover return and revert, including memory expansion,
zero-length high-offset and max-offset no-expansion, uninitialized `MLOAD`
zero-fill with memory expansion, `MLOAD`/`MSTORE`/`MSTORE8`
memory-expansion out-of-gas, explicit `INVALID` and undefined-opcode invalid
opcode, stack underflow/overflow including deep `DUP16`/`SWAP16` underflow,
standalone memory-expansion out-of-gas,
bad-jump exceptional halts, valid `JUMP`/`JUMPI`
control flow, EOF-truncated `PUSHn` immediates, invalid jumps to
`JUMPDEST`-looking bytes inside full and truncated PUSH data,
false-branch `JUMPI` ignoring such invalid destinations, `GAS`, call-context reads (`ADDRESS`,
`CALLER`, `ORIGIN`, `CALLVALUE`),
block-context reads (`COINBASE`,
`TIMESTAMP`, `NUMBER`, `GASLIMIT`, `CHAINID`, `BASEFEE`, host-supplied
`BLOCKHASH` including the 256-block boundary and invalid current/future/too-old
block numbers, transaction `BLOBHASH`, `PREVRANDAO`,
`BLOBBASEFEE`, and `BLOBHASH` out-of-range maximum-index lookup), `GASPRICE`,
host-oracled `KECCAK256` over a memory slice, zero-length high-offset and
max-offset `KECCAK256`, memory-expanding `KECCAK256` with zero padding, and
`KECCAK256` memory-expansion OOG before host-oracle lookup, `CALLDATALOAD`
at the maximum word offset returning zero, cold/warm `SLOAD`,
cold `SSTORE`, dirty no-op `SSTORE`, low-gas `SSTORE` guard including the
2301-gas allowed boundary,
set-then-reset `SSTORE` refund accounting, nonzero-to-zero `SSTORE` refund
accounting, storage-state comparison, raw
`LOG0` through `LOG4` including log memory expansion, zero-length
high-offset and max-offset no-expansion with topic recording, and log
memory-expansion OOG without emitting a log,
manual committed-log rollback and ordering checks for root-frame failure,
child-frame failure, parent-frame failure after successful child logs, and
parent/child interleaving,
`SELFBALANCE`, `BALANCE` for existing and missing accounts,
low-160-bit canonicalization for stack-supplied account/precompile addresses
across account reads, `EXTCODEHASH`, `CALL`, identity-precompile dispatch, and
`SELFDESTRUCT` beneficiaries, account-inspection opcodes against an identity
precompile address, and initial warmth/account inspection for extended BLS and
P256 precompile addresses,
successful raw `CALL`, `STATICCALL`, `CALLCODE`, and `DELEGATECALL` returndata
with output-buffer truncation plus short-returndata output-tail retention,
`CALL`/`STATICCALL`/`CALLCODE`/`DELEGATECALL` revert returndata, value transfer
to an initially empty account/new-account gas,
value-transfer call stipend and
zero-value no-stipend behavior for zero requested child gas, zero-requested-gas
`CALL` memory-expansion out-of-gas, zero-length max-offset `CALL`
input/output without memory expansion, zero-length max-offset
`CALLCODE`/`DELEGATECALL`/`STATICCALL` input/output without memory expansion,
zero-value calls to missing accounts without
materializing them, `CALL`/`STATICCALL`/`CALLCODE`/`DELEGATECALL` returndata
clearing after a subsequent empty missing-account call, missing-account `CALL`
output-buffer preservation with empty returndata,
failed `CALL` output buffer/returndata behavior for insufficient-balance,
invalid-opcode, and memory-expansion out-of-gas failures, failed
`STATICCALL`/`CALLCODE`/`DELEGATECALL` output buffer/returndata behavior for
invalid-opcode and memory-expansion out-of-gas child failures, root-frame
`CALLVALUE` balance rollback on `REVERT`, invalid opcode, and memory-expansion
out-of-gas,
value-transfer `CALL` balance commit to successful code accounts and
rollback from reverted, invalid-opcode, and memory-expansion out-of-gas code
accounts, parent-frame rollback of a successful child value-transfer `CALL`
when the parent reverts, hits invalid opcode, or runs out of gas during memory
expansion, `CALLCODE`/`STATICCALL`/`DELEGATECALL`
to a missing account with empty returndata and no account materialization, and
nonzero-value `CALLCODE` balance precondition behavior without value transfer,
including code-present insufficient-balance failure, code-present value-bearing
`CALLCODE`/`DELEGATECALL` caller-context behavior,
`CALLCODE`/`DELEGATECALL` caller-storage commit on success and rollback after
`REVERT`, invalid-opcode, and memory-expansion out-of-gas child failures,
nonzero-value self-`CALL` affordability with no net balance movement, the
static-frame distinction between allowed value-bearing `CALLCODE` and rejected
value-bearing `CALL`, static-frame propagation through zero-value `CALL`,
`CALLCODE`, and `DELEGATECALL` to rejected inner `SSTORE`/`LOG`, and the
EIP-150 all-but-one-64th child-gas cap for over-requested call gas, including
the value-stipend-after-cap case, plus
target warmth after insufficient-balance value `CALL` failure,
EIP-7702 delegation indicators for `CALL`, `CALLCODE`, `DELEGATECALL`, and
`STATICCALL`, including delegated `CODESIZE` versus authority `EXTCODESIZE`,
delegated storage-context behavior, static-frame rejection of a delegated
storage write, delegation-to-precompile executing empty code, and one-hop-only
delegation,
static-frame rejection of `CREATE`/`CREATE2`,
`RETURNDATASIZE`, and `RETURNDATACOPY`, `RETURNDATACOPY` exact-end
zero-length copying and zero-length past-end/max-offset exceptional bounds,
`CALLDATALOAD`/`CALLDATASIZE` zero-padded reads, direct `CODESIZE`/`CODECOPY`/`CALLDATACOPY`,
past-end zero padding for `CODECOPY`, `CALLDATACOPY`, and `EXTCODECOPY` while
preserving untouched memory tails, memory-expansion out-of-gas for
`RETURNDATACOPY`, `CALLDATACOPY`, `CODECOPY`, `EXTCODECOPY`, and `MCOPY`,
zero-length memory ranges for copy/hash/log operations including max-offset
`CODECOPY`/`CALLDATACOPY`/`EXTCODECOPY` and two-range `MCOPY`, `PC`/`MSIZE` including `PC` after
max-width `PUSH32`, `MSTORE8`
truncation with aligned/unaligned `MLOAD`, `EXTCODEHASH` for missing, empty, and non-empty
accounts, warm-account `EXTCODESIZE`/`EXTCODECOPY` with post-run callee-code
checks, basic `TSTORE`/`TLOAD`, transaction-boundary transient-slot cleanup
after a successful root frame plus rollback after root `REVERT`, invalid opcode,
and memory-expansion out-of-gas, transient storage commit across successful calls,
rollback after reverted call frames, `DELEGATECALL`/`CALLCODE`
caller-context ownership, `CALLCODE`/`DELEGATECALL` caller-context transient
rollback after `REVERT`, invalid-opcode, and memory-expansion out-of-gas child
failures, and static-frame `TSTORE` rejection,
overlapping `MCOPY`, deep `DUP`/`SWAP`, and raw non-commutative operand-order
probes, including signed arithmetic/bit extraction (`SDIV`, `SMOD`, `SLT`,
`SGT`, `SAR`, `SIGNEXTEND`, `BYTE`, `NOT`, `ISZERO`), high-index and
last-byte-boundary `SIGNEXTEND`, first/last/out-of-range `BYTE` boundaries,
signed division/modulo sign combinations, signed minimum/maximum comparison
boundaries, unsigned comparison/equality zero-versus-maximum boundaries,
signed minimum-integer division edges, zero-divisor/modulus
arithmetic edges, unbounded-intermediate `ADDMOD`/`MULMOD` behavior,
`ADDMOD`/`MULMOD` zero-modulus behavior, `EXP` result/gas behavior for zero-,
one-, two-, and 32-byte exponents, large and exact 255-bit boundary shifts,
out-of-range bit extraction, and `CLZ` zero/top-bit boundaries.
The `returndatacopy-oob`, `returndatacopy-zero-length-past-end`,
`ecadd-invalid-point-clears-returndata-returndatacopy-oob`,
`returndatacopy-max-offset-oob`, `returndatacopy-zero-length-max-offset-oob`,
`invalid-opcode`, `stack-underflow`,
`dup16-underflow`, `swap16-boundary-underflow`, `stack-overflow`,
`memory-expansion-oog`, `mload-max-offset-oog`, `mstore-max-offset-oog`,
`mstore8-max-offset-oog`,
`return-memory-expansion-oog`,
`revert-memory-expansion-oog`, `keccak-memory-expansion-oog-no-oracle`,
`returndatacopy-memory-expansion-oog`, `calldatacopy-memory-expansion-oog`,
`codecopy-memory-expansion-oog`, `extcodecopy-memory-expansion-oog`, `mcopy-memory-expansion-oog`,
`call-zero-requested-gas-memory-expansion-oog`, `log1-memory-expansion-oog-no-log`,
`create-initcode-memory-expansion-oog-no-nonce`,
`create2-initcode-memory-expansion-oog-no-nonce`, `sstore-low-gas-guard`, and
`bad-jump` cases intentionally
skip the gas-field comparison in the harness because Foundry's `lastCallGas()`
proxy observation reports local cost for these exceptional halts; Lean keeps
the out-of-gas-style burn semantics and the fixtures still check the halt
status/output surface.
Focused storage-gas cases also cover root-frame rollback after a refund-bearing
`SSTORE` followed by `REVERT`, `SSTORE` refund transitions for dirty current
slots with transaction-original zero, original-nonzero clear/recreate debits
and reset refunds, repeated warm dirty writes, and `SLOAD` warming a slot
before `SSTORE`.
The Forge log recorder exposes logs from reverted frames, so committed-log
rollback cases pass explicit receipt-log expectations to the Lean checker
instead of using `vm.recordLogs` as the log oracle.
The current Foundry build also does not expose a post-call transient-slot
cheatcode, so root-frame final transient-slot cleanup cases assert the Lean
final state against explicit slot expectations while using Foundry for
status/gas/output.
Access-warmth cases check that account accesses made by `BALANCE`,
`EXTCODESIZE`, `EXTCODEHASH`, and zero-length `EXTCODECOPY`, and storage-key
accesses made by `SLOAD`, remain warm in later parent work after a successful
child call, while the same accesses inside a reverted child frame are rolled
back to cold. They also check successful child `SELFDESTRUCT` beneficiary warmth
and successful child `CREATE`/`CREATE2` created-address warmth, rollback of
nested selfdestruct-beneficiary warmth and `CREATE`/`CREATE2` created-address
warmth when the enclosing child frame reverts, and pin the initial callee-frame
warmth of `ADDRESS`, `CALLER`, `ORIGIN`, and `COINBASE` account accesses.
CREATE/CREATE2 failure cases also check that initcode `REVERT`, runtime-code
size-limit failure, code-deposit out-of-gas with cleared returndata, or address
collision with cleared returndata increments the creator nonce, rolls back the
tentative account, and still leaves the would-be created address warm for later
account-access opcodes. Boundary cases check that exactly 24,576 bytes of
runtime code deploys successfully.
Oversized initcode cases check the EIP-3860 max-initcode failure path that
charges setup gas and increments the creator nonce without address-derivation
oracle assumptions.
Funded value-bearing `CREATE`/`CREATE2` cases check
created-account balance commit on success, value-transfer rollback after
initcode `REVERT`, invalid opcode, memory-expansion out-of-gas, and
code-deposit out-of-gas, collision failure with value available, and
parent-frame rollback of successful value-bearing creation. Deployment-log
cases check constructor-log commit, initcode-failure rollback, parent-failure
rollback after successful constructor logs, and parent/constructor log ordering
for `CREATE` and `CREATE2`.
The `SELFDESTRUCT` cases check post-Cancun balance transfer to existing and
previously missing beneficiaries while preserving storage and runtime code for
non-created destructing accounts, the self-beneficiary no-burn path for
pre-existing accounts, a pre-existing account remaining callable after
`SELFDESTRUCT`, a second same-transaction call to a pre-existing selfdestructed
account not transferring the original balance again, zero-balance
`SELFDESTRUCT` to a missing beneficiary not materializing an empty account,
value-bearing `SELFDESTRUCT` to a precompile beneficiary, plus
`STATICCALL` rejection of a child
`SELFDESTRUCT`, rollback of successful child storage writes and child
`SELFDESTRUCT` code/balance effects when the parent frame reverts, hits invalid
opcode, or runs out of gas during memory expansion, and the same-transaction
create-then-`SELFDESTRUCT` split where
the created account's code remains visible to `EXTCODEHASH` inside the current
frame, remains callable in that frame, and still collides with a same-salt
`CREATE2` recreation attempt before the finalized post-call account view clears
its runtime code while preserving the observed runtime code hash.
Because Lean does not compute Keccak internally, cases that inspect finalized
destroyed-account code hashes must pass the destroyed runtime-code hash through
the host Keccak table; missing entries are treated as missing host data, not as
empty-code hashes.
They also include a compiled Solidity contract with a real dispatcher, public
storage getters, nested branches, `for`/`while` loops, fixed memory arrays,
dynamic `bytes` calldata, storage mutation, an indexed event, and a
custom-error revert. Precompile cases cover `ECRECOVER`, identity, SHA-256,
RIPEMD-160, MODEXP, BLAKE2F, BN254 `ECADD`/`ECMUL`/pairing, the KZG point
evaluation precompile, `P256VERIFY`, and the EIP-2537 BLS12-381 precompiles,
including an identity-precompile low-gas failure,
low-gas failures for the host-oracled crypto precompiles, MODEXP's zero-modulus
empty-output path with a preserved output buffer, BLAKE2F invalid-length and invalid-final-flag failures,
BN254 empty-input and pairing invalid-length paths including preserved output buffers, explicitly host-oracled
BN254 invalid-point failures, BN254 invalid-point and low-gas failures with preserved
output buffers, point-evaluation invalid-length and invalid-proof
failures, BN254 invalid-point value-transfer rollback, `P256VERIFY`
invalid-length and invalid-signature empty-output paths including invalid-input
value-transfer commit, returndata clearing and preserved output buffers after
failed precompile calls including identity-precompile low-gas failure, and
exceptional `RETURNDATACOPY` after failed precompile calls clear returndata,
zero/infinity BLS operation paths, BLS MSM discount and multi-pair pairing gas,
BLS invalid-length, empty-variable-input, invalid-field-encoding, and OOG paths,
precompile `CALL` value-transfer commit/rollback behavior, identity precompile
value-bearing low-gas rollback with preserved output buffers, identity precompile
`DELEGATECALL` and value-bearing `CALLCODE`, invalid-signature `ECRECOVER` and
`P256VERIFY` invalid-length and invalid-signature empty-output paths with
preserved output buffers, KZG
point-evaluation invalid-length, invalid-proof, and low-gas failures with
preserved output buffers, `P256VERIFY` low-gas failures with preserved output buffers,
BLAKE2F invalid-final-flag and invalid-length failures with preserved output
buffers, BLS G1MSM/G2MSM/pairing empty-variable-input failures,
BLS G1ADD/G1MSM/G2ADD/G2MSM/pairing/map invalid-length failures and
G1ADD/G1MSM/G2ADD/G2MSM/pairing/map low-gas failures with preserved output buffers, and host-oracled
ECRECOVER, SHA-256, RIPEMD-160, BLAKE2F, and MODEXP low-gas failures checked without
signature/hash/result oracles, with
cryptographic digest, signature/address, MODEXP result bytes, BLAKE2F result
bytes, nontrivial BN254 result bytes, KZG proof validity, P-256 signature
validity, and BLS result bytes supplied by explicit oracles where needed. The
multi-contract cases install separate caller, worker, and
delegate library runtimes and cover `CALL`, `STATICCALL`, caught child reverts,
child storage rollback after revert, static-frame state-change rejection,
including `SSTORE` and `LOG`, `CALLCODE`, `DELEGATECALL`, value transfer,
insufficient-balance call failure, cross-account storage, account balances, and
emitted logs.
Dynamic deployment cases now cover successful `CREATE`, raw successful `CREATE`
and `CREATE2` with cleared parent returndata, code-present and nonce-only
creation collisions, `CREATE` with `STOP` initcode yielding an empty-runtime
account, successful `CREATE` rolled back by parent-frame
`REVERT`, invalid opcode, and memory-expansion out-of-gas, successful `CREATE2`
rolled back by parent-frame invalid opcode and memory-expansion out-of-gas,
zero-length high-offset and max-offset `CREATE`/`CREATE2` without memory expansion,
`CREATE`/`CREATE2` initcode revert returndata, runtime-code size-limit failure,
the exact runtime-code size boundary, and code-deposit out-of-gas failure with
returndata clearing,
`CREATE`/`CREATE2` initcode memory-expansion out-of-gas without creator nonce
increment, same-transaction `CREATE` then `SELFDESTRUCT` deletion behavior,
successful
`CREATE2`, underfunded value-bearing `CREATE`/`CREATE2` without creator nonce
increment or address-derivation oracle assumptions, and `CREATE2` address
collision by passing the needed
address-derivation Keccak preimages into Lean's hash oracle, checking the
factory's stored deployed address/result, created or colliding account
code/storage/balance/nonce, constructor/runtime/factory logs where applicable,
and gas.
The Forge profile currently leaves Foundry's `code_size_limit` unset for
deployment convenience, but raw `CREATE`/`CREATE2` runtime-size fixtures still
exercise EIP-170 rejection through the EVM execution path.
Its current runtime behavior also does not provide a useful EIP-3860 initcode
size-limit parity signal, so the `MAX_INITCODE_SIZE` guard is likewise modeled
directly in the target semantics.
EIP-7702 set-code transaction validation itself is outside this bytecode replay
harness; the suite exercises the post-authorization account-code shape
(`0xef0100 || address`) for CALL-like executing opcodes.
Exact cold/warm gas for delegated-code resolution is pinned in Lean gas examples
rather than Forge, because installing designator accounts with `vm.etch` makes
those fixture accounts warm in Foundry's observed call path.

The stateful replay runner also intercepts the Foundry cheatcode address in
Lean. The current alpha tier covers state mutation and inspection (`deal`,
`etch`, `store`, `load`, nonces), caller control (`prank`, `startPrank`,
`stopPrank`), block/env setters, access-list warm/cool helpers, log recording,
snapshots, and host-oracled `addr`/`sign` results. `expectEmit`, `expectCall`, and `label` are accepted as
permissive no-ops until assertion semantics are modeled.

## Upstream Suite Direction

Pinned suites are listed in `foundry-suites.toml`; checkouts live under
`tests/.foundry-suites/` and are intentionally not committed.

Useful corpus commands:

```sh
python3 tests/bin/foundry_corpus.py list
python3 tests/bin/foundry_corpus.py fetch --suite solmate
python3 tests/bin/foundry_corpus.py scan --suite solmate
python3 tests/bin/foundry_corpus.py forge --suite local-forge-parity -- --list
```

The replay path should first import `forge build` artifacts, deploy the test
contract, run `setUp()`, execute one test function in a persistent per-test
chain state, intercept the Foundry cheatcode address in Lean, and then compare
status, returndata, logs, storage/account state, balances, nonces, deployed
code, and meaningful gas observations. Forked tests, filesystem/FFI cheatcodes,
RPC-dependent tests, and fuzz or invariant campaigns stay outside the required
pass set until deterministic unit-test replay is stable.
