# L01 CheckedSolidity

## Purpose

`CheckedSolidity` is the verified Solidity input boundary. It is not merely
"accepted source"; it is a source artifact paired with the evidence later passes
are allowed to rely on.

This layer answers:

```text
Is this Solidity program in scope, and what static facts have been established?
```

## Language Shape

The syntax can remain close to `Source`, but it should be wrapped in a checked
program artifact.

The artifact should eventually carry:

- resolved identifiers and scopes, preferably with unique local handles rather
  than bare strings;
- function, modifier, event, error, and storage declarations;
- type facts for expressions, lvalues, calls, and returns;
- supported-feature evidence;
- inheritance and override resolution if those features enter scope;
- modifier validity and placeholder/body-position facts;
- ABI-relevant function and event metadata;
- static facts needed by storage and call lowering.

The important shape is:

```text
named source AST
  -> resolved checked AST
```

After this layer, expression and lvalue uses should refer to explicit local
handles, function identities, event identities, error identities, or storage
locations. Bare source names should not remain in the core checked artifact
except as optional diagnostic metadata.

## Semantics

Usually this layer should reuse source semantics. A checked program has the same
behavior as its source program; it just carries static evidence.

Do not introduce a new semantics unless the checked language explicitly narrows
undefined behavior or gives a different error model. If that happens, the
relationship to source semantics must be a theorem, not a convention.

## Wellformedness Boundary

This is where static wellformedness belongs:

- no unresolved names;
- no illegal shadowing if the chosen subset disallows it;
- all expressions have types;
- assignment targets are valid;
- calls have compatible arguments and returns;
- modifiers are syntactically and semantically valid enough to desugar;
- storage declarations have stable identities;
- unsupported source features are rejected.

These facts should be intrinsic to the checked artifact, not defined as "later
compiler pass succeeds."

The checker boundary should also keep these notions separate:

- parser success: text became a source AST;
- accepted-source checking: the AST became a resolved checked artifact;
- compiler success: later passes returned lower artifacts;
- certificate checking: a package of evidence was accepted.

A certificate checker can combine these in a convenient API, but its soundness
theorem should unpack back to the AST-level facts above.

## Outgoing Pass

`CheckedSolidity -> DesugaredSolidity` removes Solidity-native surface structure
while preserving checked-source behavior.

The preservation theorem should say that evaluating the desugared program
matches evaluating the checked source program under the same environment and
runtime assumptions.
