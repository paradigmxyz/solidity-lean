# L02 DesugaredSolidity

## Purpose

`DesugaredSolidity` is still Solidity-level, but it removes rich source surface
forms so later lowering does not need to understand every Solidity convenience.

This layer answers:

```text
What smaller Solidity-core program has the same behavior as the checked source?
```

## Language Shape

It should retain source-like concepts:

- typed Solidity expressions;
- lexical block structure;
- functions or a normalized function representation;
- locals and source-level variables;
- returns, reverts, loops, conditionals, and blocks;
- source-level storage/event/call concepts.

It should remove or normalize:

- modifiers by expanding them into ordinary body structure;
- inheritance/override choices once they are checked;
- constructors/fallback/receive into a uniform callable shape if useful;
- tuple/destructuring and declaration sugar;
- implicit source conveniences that obscure evaluation order.

It should not introduce Yul-only constructs. If a transformation literally
introduces Yul `switch`, that belongs later.

## Semantics

The semantics should still look like Solidity semantics over typed source
values. It should be simpler than `Source`, but not yet Yul-shaped.

The evaluator should make it easy to state that desugaring preserves behavior:

- modifier expansion preserves return/revert/fallthrough behavior;
- normalized calls target the same checked function identities;
- expression and statement sugar has the same result as the source construct.

## Wellformedness Boundary

This layer should require:

- no remaining unsupported source sugar;
- modifier expansion facts;
- normalized declaration/function shape;
- checked facts preserved or translated from `CheckedSolidity`;
- no generated names capture source names.

## Outgoing Pass

`DesugaredSolidity -> AbstractYul` changes the scoping/control model from
Solidity-like to Yul-like. This is where we stop looking like Solidity and start
looking like a compiler IR.

The theorem should say the Yul-shaped abstract program refines or matches the
desugared Solidity behavior.
