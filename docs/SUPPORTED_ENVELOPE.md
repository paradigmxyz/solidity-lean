# Supported envelope

What the generic certification (`SolidCore.Verify.Generic.Expected`, docs/GENERIC_INTERFACE.md)
covers today, feature by feature. A contract that uses anything BLOCKED, or anything the envelope
does not classify, comes out **BLOCKED with the reason**, never Certified. A contract inside the
envelope is Certified only when the kernel checks `Expected` over the exact fresh bytes; the
envelope is a gate in front of the proof, not a substitute for it. Nothing here claims automatic
verification: loops need supplied invariants and ranking certificates, and specifications are
reviewed inputs.

Statuses: **Supported** (no premise beyond the statement), **Supported-with-premise** (the premise
is part of the statement or its recorded coverage, and the report lists it), **BLOCKED**.

The machine-readable list is `Verify/Generic/envelope.json`; the table below is generated from it.
`Verify/Generic/envelope_check.py` applies it to solc's AST:

```sh
solc --ast-compact-json Foo.sol > ast.json
python3 Verify/Generic/envelope_check.py ast.json --contract Foo \
  [--entry 'transfer(address,uint256)']... [--loop-certificates N] [--tier runtime|lifecycle]
```

It walks the declared entrypoints (default: every public and external function and getter) and
everything they reach (internal and library functions, modifiers, state variables), plus the
contract's inheritance, fallback/receive and immutables, matches every AST node against the
features, and blocks any node or call type the envelope does not classify (default deny). It
prints `status` (`Supported`, `Supported-with-premise` or `BLOCKED`), `blocked` (feature, reason,
source location), `premises`, `entries` and `excluded` (public functions outside the statement),
and exits 3 when BLOCKED.

## Tier and context

`Expected` is the **runtime tier**: every valid call from any storage the spec admits. It does
not state constructor establishment of the spec's invariant, its preservation by every
entrypoint, or reentrant post-states (`lifecycle`: BLOCKED). The caller is a parameter of the
statement (`spec.Contexts`); the contract's address (0x1000) and the block and transaction of
`Target.message` are fixed and recorded as coverage.

## Features

| Feature | What | Status | Premise or reason |
|---|---|---|---|
| `storage-scalar` | Value-type state variables (uint/int/bool/address/bytesN) | **Supported** | none (evidence: Certified/counter, Certified/mulx (compiled), Contracts/Counter/ShapeExport.lean) |
| `mapping` | One-level mappings with uint256 values | **Supported-with-premise** | Keccak-256 separation scoped to each call's footprint (ScopedSep), stated inside spec.Valid at the call; or a named HashInj assumption (conditional tier). Never a global separation premise. (evidence: Contracts/UniswapV2/ERC20/Certified/Transfer.lean, Certified/verify_token) |
| `mapping-other-values` | mappings whose values are not uint256 (such as mapping(address => bool)) | **BLOCKED** | mappings whose values are not uint256 (such as mapping(address => bool)): Generic.eraseFn gives no tree (generic driver probe: Registry) |
| `nested-mapping` | nested mappings | **BLOCKED** | nested mappings: only slot-level and key-level results under scoped separation exist (Contracts/UniswapV2/ERC20/Nested), no end-to-end certificate; a global NestedSlotsSeparated premise is not accepted |
| `checked-arith` | Checked +, -, * and comparisons, with Panic(0x11) on overflow | **Supported** | none (evidence: Certified/counter (Panic 0x11 in allowed), Certified/mulx, transfer's SafeMath reverts) |
| `arith-other` | division, modulo, exponentiation, bitwise operators and shifts | **BLOCKED** | division, modulo, exponentiation, bitwise operators and shifts: no certified contract exercises them end to end |
| `unchecked` | unchecked blocks with wrapping + and - | **Supported** | none (evidence: transfer: the port of SafeMath.add/sub (unchecked, then require) is in the certified scope) |
| `unchecked-mul` | wrapping multiplication in unchecked blocks | **BLOCKED** | wrapping multiplication in unchecked blocks: no certified contract exercises it |
| `events` | emit of events with value-type fields (LOG0-LOG4) | **Supported** | none (evidence: Certified/events (certified), transfer's Transfer log) |
| `internal-calls` | Calls of internal and private functions, and internal library functions (using-for) | **Supported** | none (evidence: Certified/bank (compiled), transfer's _transfer and SafeMath (checker with contexts, AssembleCtx)) |
| `public-called-internally` | a public function called internally | **BLOCKED** | a public function called internally: Generic.eraseFn gives no tree (generic driver probe: Band) |
| `recursion` | recursive internal calls | **BLOCKED** | recursive internal calls: the checker with contexts types each internal function once per call site; no recursion support |
| `loops` | loops | **BLOCKED** | loops: the generic source stage (Generic.eraseFn/check) is loop-free, so supplied invariants have no generic consumer yet; loop certificates exist only on contract-specific routes (Contracts/VerifyCounter, Contracts/CallSqrt). The gate also blocks a loop without a supplied invariant/ranking certificate (evidence: generic driver probe at solar 902cccc2 / solidity-lean bc6da61b (StepSum, EmptyRevert)) |
| `external-calls` | calls to other contracts or accounts (external, low-level call/delegatecall/staticcall, transfer/send) | **BLOCKED** | calls to other contracts or accounts (external, low-level call/delegatecall/staticcall, transfer/send): Expected runs the source in a closed world; the open-world shape (Shapes.OpenFunctional) is never Certified |
| `reentrancy` | reentrancy | **BLOCKED** | reentrancy: needs external calls and the actual post-state of a reentrant call; not stated |
| `create` | contract creation (new C, CREATE) | **BLOCKED** | contract creation (new C, CREATE): source and assembly nodes exist (CreateNode, AssembleCreate) but no certificate composes them |
| `create2` | salted creation (new C{salt | **BLOCKED** | salted creation (new C{salt: s}, CREATE2): not certified end to end |
| `new-array` | memory array allocation | **BLOCKED** | memory array allocation: not certified |
| `gas-bound` | Constant gas bound per valid call, below 2^64 | **Supported** | observable-equality bound: from the bound on, the bytes' observable equals the source's; an empty revert is not told apart from out-of-gas, so this is not a no-out-of-gas guarantee (evidence: every certified instance) |
| `constructor` | Constructors without parameters | **Supported-with-premise** | runtime tier only: the init code is not covered and valid calls range over any storage the spec admits (storage that writes the constructor's slots); constructor establishment of the spec's invariant is not stated (evidence: Certified/verify_counter, Certified/verify_token) |
| `constructor-args` | constructors with parameters | **BLOCKED** | constructors with parameters: Wide.DeployedAt runs the constructor with no arguments, so no generic route reaches a deployed state (generic driver probe: Clamp, StepSum) |
| `lifecycle` | lifecycle certificate (constructor establishes the invariant, every entrypoint preserves it, reentrant post-states) | **BLOCKED** | lifecycle certificate (constructor establishes the invariant, every entrypoint preserves it, reentrant post-states): not provided; Expected is the runtime tier |
| `immutables` | immutable variables | **BLOCKED** | immutable variables: their values are patched into the runtime bytes by the constructor; not modelled |
| `constants` | constant state variables | **BLOCKED** | constant state variables: Generic.eraseFn gives no tree for functions reading them (generic driver probe: Band) |
| `assembly` | inline assembly | **BLOCKED** | inline assembly: not certified (assembly create2 has a source node only) |
| `modifiers` | Function modifiers | **Supported** | none (evidence: Certified/verify_token (onlyOwner)) |
| `require-revert-string` | require/revert with a string reason (Error(string)) | **Supported** | none (evidence: transfer's ds-math-sub-underflow) |
| `custom-errors` | custom errors | **BLOCKED** | custom errors: no certified contract |
| `try-catch` | try/catch | **BLOCKED** | try/catch: external calls |
| `payable` | payable functions accepting value | **BLOCKED** | payable functions accepting value: no certified contract (a call with value to a non-payable function is supported and reverts) |
| `fallback-receive` | fallback and receive functions | **BLOCKED** | fallback and receive functions: not certified |
| `dynamic-abi` | dynamic ABI types (string, bytes, arrays, structs) in parameters or returns | **BLOCKED** | dynamic ABI types (string, bytes, arrays, structs) in parameters or returns: valid calls are clean static argument words only |
| `storage-aggregates` | structs, arrays, strings and bytes in storage | **BLOCKED** | structs, arrays, strings and bytes in storage: no certified contract |
| `inheritance-code` | inheriting from a contract with code | **BLOCKED** | inheriting from a contract with code: no certified contract (inheriting interfaces only is accepted) |
| `external-library` | public/external library functions (DELEGATECALL to a linked library) | **BLOCKED** | public/external library functions (DELEGATECALL to a linked library) |
| `selfdestruct` | selfdestruct | **BLOCKED** | selfdestruct |
| `caller` | msg.sender | **Supported-with-premise** | the statement covers the contexts in spec.Contexts (a caller parameter); coverage is reported, and a single-caller coverage is never reported as any-caller |
| `msg-other` | msg.value, msg.data and msg.sig reads | **BLOCKED** | msg.value, msg.data and msg.sig reads: not certified |
| `block-tx-env` | block.* and tx.* reads | **Supported-with-premise** | the block and transaction are Target.message's fixed values, recorded in coverage, not quantified |
| `keccak` | keccak256 and abi.encode of value types | **Supported-with-premise** | EthLib's Keccak-256 on both sides; no injectivity assumed by the translation (Certified/abi_hash, compiled) |
| `other-builtins` | other builtins (ecrecover, sha256, ripemd160, addmod, mulmod, gasleft, blockhash, abi.decode, abi.encodePacked, abi.encodeWithSelector, ...) | **BLOCKED** | other builtins (ecrecover, sha256, ripemd160, addmod, mulmod, gasleft, blockhash, abi.decode, abi.encodePacked, abi.encodeWithSelector, ...) |

## Gate receipts

`envelope_check.py` with solc 0.8.35 on the repository's fixtures and on one negative per blocked
family (exit 0 unless BLOCKED, exit 3 when BLOCKED):

| Contract | Entries | Result |
|---|---|---|
| Certified/counter Counter | all | Supported |
| Certified/mulx Main | all | Supported |
| Certified/events Events | all | Supported-with-premise (caller) |
| Certified/bank Bank | all | Supported-with-premise (mapping, caller) |
| Certified/verify_token Token | all | Supported-with-premise (mapping, constructor, caller) |
| Certified/abi_hash AbiHash | all | Supported-with-premise (keccak) |
| Certified/verify_counter Counter | `bump`, 1 loop certificate | BLOCKED (loops: no generic consumer of loop certificates; constructor-args) |
| UniswapV2ERC20 (port) | `transfer(address,uint256)` | Supported-with-premise (mapping, constructor, caller); 12 public functions excluded |
| UniswapV2ERC20 (port) | all | BLOCKED (nested-mapping, storage-aggregates, other-builtins, unclassified-call) |
| any | `--tier lifecycle` | BLOCKED (lifecycle) |
| negatives | inheritance with code, nested mapping, immutable, low-level call, inline assembly, division, recursion, `new`, custom error, payable, `string` parameter, `msg.value`, loop, unchecked `*`, constructor with parameters, constant, `mapping(address => bool)`, public function called internally | BLOCKED, each with its feature |

The generic driver's probe of the held-out contracts at solar 902cccc2 / solidity-lean bc6da61b found stage-check gaps inside the envelope's own features: `Tree.canon` does not orient `gt a b` as `lt b a` (a `>` against storage can fail the source stage), and the MIR symbolic run of a public pure function with early returns can be undefined. Such a contract passes the gate and still fails its proof; the driver reports the per-function verdict as BLOCKED, never Certified.
