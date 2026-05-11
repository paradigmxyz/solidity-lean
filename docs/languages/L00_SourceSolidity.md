# L00 SourceSolidity

## Purpose

`SourceSolidity` is the broad Solidity-facing AST and source semantics. It
preserves user-visible program shape before the verified compiler narrows the
language.

This layer should be generous about syntax and conservative about proof claims.
Unsupported features can exist in the source AST; they are rejected by
`SourceSolidity -> ValidSolidity`.

## Basic Syntax

Expected syntax includes:

- contracts, inheritance lists, constructors, fallback, receive, and ordinary
  functions;
- source declarations for storage fields, events, errors, modifiers, structs,
  enums, and using-directives as the scope expands;
- source expressions: literals, identifiers, member access, indexing, calls,
  arithmetic, comparisons, boolean operators, ternary, tuple expressions, casts,
  and builtins such as `msg.sender`;
- source statements: blocks, variable declarations, assignments, compound
  assignments, `if`, `for`, `while`, `break`, `continue`, `return`, `revert`,
  `emit`, `try/catch`, `unchecked`, and inline assembly if we later choose to
  model or reject it;
- unresolved names and overloaded names exactly as they appear in source.

The source AST may contain features outside the verified fragment. This layer is
not the accepted subset.

## Semantics

The source semantics should explain Solidity behavior directly:

- expression evaluation and Solidity evaluation order;
- checked and unchecked arithmetic;
- source lexical scopes and local variables;
- storage at the Solidity abstraction level;
- return, revert, break, continue, and fallthrough behavior;
- logs/events, returndata, calldata, `msg.*`, `block.*`, and external
  environment as source-level concepts;
- function and modifier behavior before compiler lowering.

The source semantics should not mention generated Yul, selectors, event topics,
storage slots, ABI buffers, stack depth, bytecode offsets, or compiler success.

## Incoming Pass

There is no compiler pass into `SourceSolidity`. Possible ingestion paths are
outside the compiler theorem unless separately verified:

- a Lean parser that returns `SourceSolidity.Program`;
- an external parser whose output is checked by Lean;
- hand-written ASTs for early proof work.

Parser success is not compiler correctness. A text-level theorem should be added
only after the parser or certificate checker has its own soundness theorem.

## Outgoing Pass: SourceSolidity -> ValidSolidity

This pass is the Solidity front-end checker. It should:

- resolve names and scopes;
- resolve overloads to source declaration identities;
- check inheritance, override, and `super` legality;
- check modifier legality;
- check expression, lvalue, return, emit, revert, and call types;
- check visibility, mutability, data-location, and payability rules;
- enforce the current verified Solidity fragment;
- produce a `ValidSolidity` artifact or fail with a source-level error.

It should not:

- desugar modifiers;
- lower control flow;
- assign storage slots;
- compute function selectors or event topics;
- allocate memory or ABI buffers;
- inspect whether later compiler passes happen to succeed.

The main theorem should say successful checking produces a valid artifact whose
behavior is the source behavior for the same program. Completeness can be added
for whatever validity predicate we choose to expose.
