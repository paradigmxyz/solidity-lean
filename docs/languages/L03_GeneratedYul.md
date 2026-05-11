# L03 GeneratedYul

## Purpose

`GeneratedYul` is the concrete Yul subset emitted by our compiler. It is not a
model of arbitrary user-written Yul.

One-line distinction from `AbstractYul`:

```text
Yul-like control/local binding, concrete Yul/EVM builtins and layout.
```

## Change From Previous Layer

Compared with `AbstractYul`, this layer:

- replaces typed abstract storage with concrete `sload`/`sstore` and slot
  formulas;
- replaces typed returns and reverts with memory buffers and byte lengths;
- replaces typed events with concrete topics/data buffers and `logN`;
- replaces abstract external calls with concrete Yul `call`, `staticcall`,
  `delegatecall`, or excluded-profile assumptions;
- introduces ABI calldata decoding and returndata encoding;
- introduces function selector dispatch for externally callable functions;
- introduces concrete memory discipline.

It still has structured Yul-like control and local variables. It does not yet
have stack labels, byte offsets, or EVM program counters.

## Basic Syntax

Expected generated subset:

- blocks;
- `let` declarations;
- assignment;
- `if`;
- `switch`;
- `for` only if the compiler emits it;
- generated helper functions only if the backend supports them cleanly;
- concrete builtin calls from an explicit profile, such as:

```text
add, sub, mul, lt, gt, eq, iszero
mload, mstore
calldataload, calldatasize, callvalue, caller
sload, sstore
keccak256
log0, log1, log2, log3, log4
call, staticcall, delegatecall
return, revert
gas
```

The supported builtin set should be profile-controlled. Early profiles can be
gasless, single-contract, no-external-call, no-dynamic-ABI, or whatever the
theorem actually covers.

## Semantics

The semantics should be direct for the generated subset:

- Yul local scopes;
- concrete memory;
- concrete storage slots;
- calldata and returndata byte arrays;
- concrete logs;
- return/revert byte-buffer exits;
- builtin behavior according to the chosen profile;
- external host behavior through named relations when not modeled exactly.

It should not interpret arbitrary Yul. Generated-subset `WF` should reject
constructs the compiler never emits or the proofs do not cover.

## Incoming Pass: AbstractYul -> GeneratedYul

This pass is layout and concrete Yul generation.

Transformations:

- compile abstract external entry points into selector dispatch;
- decode calldata arguments using ABI rules;
- encode return values using ABI rules;
- encode custom errors, panic errors, and raw reverts into memory;
- encode events into topics and data buffers;
- lower source storage identities into slot formulas;
- lower mappings and dynamic storage access into `keccak256` slot formulas;
- lower typed arithmetic into concrete word operations plus overflow checks;
- lower abstract storage effects into `sload` and `sstore`;
- lower abstract calls into concrete Yul call builtins or reject unsupported
  call profiles;
- introduce helper functions for repeated encoding/layout patterns if useful;
- establish a memory discipline for scratch space, free memory, returndata, and
  overlapping helper buffers.

The pass should produce:

- generated Yul syntax;
- generated-subset `WF`;
- builtin/profile assumptions;
- layout facts needed by the preservation theorem.

The theorem should connect each abstract effect to the concrete Yul sequence
implementing it:

```text
compile abstract = ok yul
  implies GeneratedYul.behavior yul refines AbstractYul.behavior abstract
  under named profile/layout/host assumptions.
```

## Outgoing Pass: GeneratedYul -> StackCfg

The next pass removes structured Yul locals and control, replacing them with a
stack-machine CFG with explicit labels, block signatures, and stack effects.
