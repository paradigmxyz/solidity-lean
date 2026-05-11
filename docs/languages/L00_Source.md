# L00 Source

## Purpose

`Source` is the Solidity-facing language. It preserves the user-visible
program shape and is the semantic starting point for the end-to-end theorem.

This layer should be generous about syntax and conservative about claims. It can
represent Solidity features before we know how to verify all of them. The
verified subset is not defined here; it is defined by the checker into
`CheckedSolidity`.

## Language Shape

Expected constructs:

- contracts, functions, constructors, fallback and receive functions;
- source expressions with Solidity operators and evaluation rules;
- statements such as blocks, declarations, assignment, conditionals, loops,
  returns, reverts, event emissions, and unchecked blocks;
- source-level declarations for storage fields, events, errors, modifiers,
  inheritance, and ABI-visible functions as the scope expands.

The language may be richer than the verified subset. Unsupported constructs
should be rejected by `Source -> CheckedSolidity`, not removed from `Source`
just to make early proofs easy.

## Semantics

The source semantics should explain Solidity behavior directly:

- expression evaluation and checked/unchecked arithmetic;
- local environment and source lexical scopes;
- storage, calldata, memory, return data, logs, and external environment at the
  Solidity abstraction level;
- function call behavior as Solidity behavior, not Yul dispatch;
- return, revert, break, continue, and fallthrough behavior.

The source semantics should not mention generated Yul, stack depth, bytecode
offsets, or compiler success.

## Wellformedness Boundary

`Source` can define parser-level or syntax-level wellformedness, but semantic
wellformedness for the verified compiler belongs in `CheckedSolidity`.

Examples of facts that should not be assumed at this layer:

- names are resolved;
- expressions are typed;
- modifiers are valid;
- storage layout is known;
- the program is inside the verified subset.

## Outgoing Pass

`Source -> CheckedSolidity` should check the program and produce a checked
artifact. Its theorem should say successful checking creates the declared
checked facts for the same source behavior.

The pass should be independent of later compiler success. A program should not
be checked merely because later passes happen to compile it.

Until there is a Lean-verified parser, the public compiler theorem should be
AST-level:

```text
Source.Program -> CheckedSolidity.Program -> ... -> Evm behavior
```

Text parsing, external Solidity parsing, Forge tests, and certificate loading
can feed that AST, but they need their own soundness statements before they are
part of the verified claim.
