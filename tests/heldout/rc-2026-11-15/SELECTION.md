# Held-out set for the 2026-11-15 release candidate

Written before any compiler, gate or driver run on these files. Selected by the acceptance
reviewer, independently of the lanes that produce proofs; none of the three was used as a fixture
or probe in solidity-lean or solar before this commit (searched both trees for the contract names
and bodies: a different `SimpleStorage`, a `bytes32 => bytes32` mapping, appears in solar's
`testdata/Optimism.sol`; nothing else matched).

## Source and license

All three come from Solidity by Example, https://github.com/Cyfrin/solidity-by-example.github.io
at commit 5bcdca0239409d7336a07b66a6fca8d0bcc710e6 (2026-01-20), MIT License (copy in
`upstream/LICENSE`, Copyright (c) 2018 Tasuku Nakamura), every file `SPDX-License-Identifier: MIT`.
The unmodified upstream files are in `upstream/`.

| Case | File | Upstream path | Change from upstream |
|---|---|---|---|
| H1 | `SimpleStorage/SimpleStorage.sol` | `contracts/src/state-variables/SimpleStorage.sol` | NatSpec `@custom:` lines added only |
| H2 | `ViewAndPure/ViewAndPure.sol` | `contracts/src/view-and-pure-functions/ViewAndPureFunctions.sol` | NatSpec `@custom:` lines added only |
| H3 | `Mapping/Mapping.sol` | `contracts/src/mapping/Mapping.sol` | NatSpec `@custom:` lines added; the file's second contract, `NestedMapping`, dropped (nested mapping with bool values: BLOCKED by the envelope; the driver takes one contract) |

Removing every line containing `@custom:` from each file gives the upstream file byte for byte
(H3: its lines 1-23). `SHA256SUMS` pins every file here.

## Why these three

Each is a complete, ordinary contract, chosen for being plausibly inside the supported subset of
the generic driver at solar c09510a3 / 1844041e (`tools/certify/generic.py`, `envelope()`) and
solidity-lean 44572c15 (`docs/SUPPORTED_ENVELOPE.md`), and for covering features the accepted
Flag positive does not (it has no constructor, mapping, checked arithmetic or return value):

- H1 SimpleStorage: one scalar `uint256`, a setter and a getter with a return value. No
  constructor. Features: storage-scalar, a returned value. Predicted: Supported; the likeliest
  to certify.
- H2 ViewAndPure: a state variable with an initializer (`x = 1`, so the init code runs a
  constructor without parameters), a `view` and a `pure` function with checked `+`
  (Panic 0x11 on overflow). Features: storage-scalar, checked-arith, constructor
  (Supported-with-premise: runtime tier only, over any storage the spec admits; that the
  constructor establishes `x == 1` is not claimed). Predicted: Supported-with-premise (constructor).
- H3 Mapping: one `mapping(address => uint256)` with get, set and `delete`. Features: mapping
  (Supported-with-premise: Keccak-256 separation scoped to each call's footprint). Predicted:
  Supported-with-premise (mapping). Highest risk of the three: no accepted positive has a mapping
  yet, and `delete` of a mapping entry has no certified instance.

All three: no loop, external call, assembly, inheritance, import, payable function, custom error,
dynamic ABI type, immutable or constant, `msg.sender`, or block or transaction read (in code or
in specs). Excluded on purpose: Flag, E6, the ERC20 fixtures, Counter (including Solidity by
Example's own `first-app/Counter.sol`), Uniswap, anything GPL or AGPL (OpenZeppelin's Ethernaut
levels were considered and rejected for their AGPL-3.0 license), `IfElse` (public pure functions
with early returns: a documented gap of the generic stage, so not plausibly inside),
`FunctionModifier` (recursion) and `Enum` (enum parameter decoding, no certified instance).

## Specs

Minimal: each function states when it must succeed (`@custom:succeeds-if`, which the driver
requires for non-vacuity) and what it returns or writes (`@custom:ensures`). Spec arithmetic is
over mathematical integers, so `x + y <= type(uint256).max` is exactly the non-overflow condition.
The specs state no frame (H3 says nothing about other keys): the translation claim (fresh bytes
behave as the source) covers the whole observable; the source-property claim is only what each
ensures says. The getters the compiler generates (`num()`, `x()`, `myMap(address)`) carry no spec.

## How to run (for the held-out runner)

One driver run per case at the RC driver pin, default runtime tier, NatSpec spec, contract named
explicitly:

| Case | Source | `--contract` |
|---|---|---|
| H1 | `tests/heldout/rc-2026-11-15/SimpleStorage/SimpleStorage.sol` | `SimpleStorage` |
| H2 | `tests/heldout/rc-2026-11-15/ViewAndPure/ViewAndPure.sol` | `ViewAndPure` |
| H3 | `tests/heldout/rc-2026-11-15/Mapping/Mapping.sol` | `Mapping` |

Expected negative exits on each case, from its own run or a reuse labelled as such: requesting the
lifecycle tier must not exit 0 (BLOCKED or strict-tier rejection), and a replay of the record with
any claim edited must be rejected. Whatever a run reports (Certified, BLOCKED or REJECTED) is the
result: a case is never edited, swapped or re-specified after a run to make it pass. A spec found
wrong after a run is reported with that run, and a corrected case is a new case with its own
rationale.
