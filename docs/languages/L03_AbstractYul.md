# L03 AbstractYul

## Purpose

`AbstractYul` is Yul-shaped control and scoping with typed abstract effects.

One-line distinction:

```text
Yul control and local binding, Solidity-typed abstract operations.
```

This is the replacement for a vague `Control` plus pre-Yul `Layout` split. It
should be close enough to Yul that control/scoping translation is mostly done,
but abstract enough that layout, ABI encoding, and concrete memory/storage
operations are not baked into every high-level theorem.

## Language Shape

Expected syntax:

- blocks;
- `let`-style local bindings;
- assignment to locals;
- `if`, `switch`, loops, and structured blocks;
- generated temporary names with freshness facts;
- procedures or labels if useful for functions/internal calls;
- explicit return and revert exits;
- explicit evaluation order.

Abstract effects may include typed operations such as:

```text
ReadLocal(x)
WriteLocal(x, value)
StorageRead(field, keys)
StorageWrite(field, keys, value)
Emit(eventId, typedArgs)
ExternalCall(target, selector, typedArgs, value)
Return(typedValues)
Revert(errorId, typedArgs)
```

These are not concrete Yul builtins yet.

## Semantics

The semantics should be operational and Yul-like:

- block-scoped locals;
- explicit evaluation order;
- explicit control exits;
- abstract storage/call/log/return/revert operations over typed values;
- no Solidity lexical lookup;
- no byte offsets, stack depth, or opcode semantics.

This layer should make source lexical scope disappear. It should use an explicit
environment or generated local namespace that is closer to Yul than Solidity.

Hashing, logs, external calls, and host behavior should be named assumptions or
relations at this level. For example, an abstract `ExternalCall` effect should
not silently claim exact EVM call semantics; it should expose the relation that
the `AbstractYul -> GeneratedYul` theorem must preserve or refine.

## Wellformedness Boundary

`AbstractYul` should own:

- generated-name freshness;
- no unbound locals;
- scoped let/assignment discipline;
- typed abstract operation arguments;
- procedure/function target closure if procedures exist;
- structured-control wellformedness.

It should not own:

- concrete ABI head/tail offsets;
- memory pointer arithmetic;
- concrete storage slot formulas;
- `mstore`, `sload`, `call`, `logN`, or other Yul builtin details;
- stack-depth facts.

## Outgoing Pass

`AbstractYul -> GeneratedYul` lowers typed abstract effects into concrete
generated Yul operations.

This is where layout lives:

- abstract storage locations become slot/hash formulas and `sload`/`sstore`;
- typed returns/reverts become memory buffers plus `return`/`revert`;
- typed events become topics/data buffers plus `logN`;
- external calls become ABI-encoded call data and concrete Yul `call`;
- function dispatch can become Yul `switch`.

The theorem should connect each abstract effect to the generated concrete Yul
sequence that implements it.

This pass should also introduce the first concrete assumptions for ABI, storage
layout, hashing, logs, and external calls as named predicates. If the first
slice excludes one of these features, the exclusion should be visible in
`AbstractYul` or `GeneratedYul` wellformedness rather than hidden in a proof.
