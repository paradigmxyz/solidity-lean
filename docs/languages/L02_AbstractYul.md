# L02 AbstractYul

## Purpose

`AbstractYul` is the first compiler IR. It is Yul-shaped control and scoping
with Solidity-typed abstract effects.

One-line distinction:

```text
Yul-like control/local binding, but source-typed abstract operations.
```

This is where source conveniences are compiled away. It is not valid Solidity
and not concrete Yul.

## Change From Previous Layer

Compared with `ValidSolidity`, this layer:

- removes Solidity lexical lookup from runtime semantics;
- replaces source expressions with explicit evaluation order;
- lowers modifiers, short-circuit, ternary, compound assignments, and call
  evaluation into explicit control/effect structure;
- makes abrupt completion explicit: normal, return, revert, break, continue, or
  any smaller set after loop lowering;
- introduces generated locals and Yul-like blocks;
- represents storage, events, calls, errors, and returns as typed abstract
  effects.

It still does not know concrete ABI, storage layout, selectors, topics, memory
buffers, stack depth, or byte offsets.

## Basic Syntax

Expected syntax:

- programs containing procedures or function-like blocks;
- Yul-like blocks;
- `let` bindings for generated locals;
- assignment to generated locals;
- `if`, `switch`, loops, and structured sequencing;
- explicit completion results:

```text
Normal
Return(typedValues)
Revert(errorId, typedValues)
Break(loopTarget)
Continue(loopTarget)
```

- typed primitive expressions over source-level words, booleans, addresses, and
  other accepted source values;
- abstract effects:

```text
ReadStorage(storageId, keys)
WriteStorage(storageId, keys, value)
Emit(eventId, indexedArgs, dataArgs)
ExternalCall(target, value, callKind, typedArgs)
ReturnValues(typedValues)
RevertError(errorId, typedArgs)
ReadEnv(field)
```

The exact syntax should stay small. Add an abstract effect only when the
`AbstractYul -> GeneratedYul` pass needs to lower it.

## Semantics

The semantics should be operational and Yul-like:

- block-scoped generated locals;
- explicit evaluation order;
- explicit completions;
- abstract storage, call, log, return, and revert effects;
- typed values rather than byte arrays when possible;
- transactional behavior for revert.

Rollback is not optional. If this layer lets a program write storage or emit a
log before a later revert, the semantics must either use transactional substate
or a journal that commit/revert consumes. Otherwise the Solidity proof will fail
on examples like `withdraw`.

## Incoming Pass: ValidSolidity -> AbstractYul

This is the big source-to-IR lowering pass.

Transformations:

- compile each valid function body into an AbstractYul procedure;
- compile modifiers by composing their prelude, body placeholder, and postlude
  with explicit completion behavior;
- compile short-circuit `&&` and `||` into explicit branch control;
- compile ternary expressions into branch control with generated locals;
- compile compound assignments and increments/decrements into explicit read,
  operation, write, and result-value structure;
- compile high-level internal calls to procedure calls;
- compile high-level external calls to typed abstract external-call effects;
- compile `for`, `while`, `break`, and `continue` into structured control with
  explicit completion propagation;
- compile `return`, `revert`, and `emit` into typed abstract exits/effects;
- compile checked arithmetic into abstract checked operations or explicit
  overflow branches.

Non-transformations:

- do not compute ABI selectors or event topics;
- do not decode calldata into concrete byte offsets;
- do not encode returns, errors, or event payloads into memory;
- do not choose storage slots or mapping hash formulas;
- do not introduce EVM stack layout.

The preservation theorem should be recursive over valid Solidity syntax:

```text
compile valid = ok abstract
  implies AbstractYul.behavior abstract refines ValidSolidity.behavior valid.
```

For early slices, the theorem can restrict source profiles, but the restriction
must live in `ValidSolidity` validity or in explicit pass hypotheses.

## Outgoing Pass: AbstractYul -> GeneratedYul

The next pass lowers typed abstract effects into concrete generated Yul. It is
the home for layout, ABI, selector dispatch, concrete memory, storage slots,
hashing, logs, calls, return buffers, and revert buffers.
