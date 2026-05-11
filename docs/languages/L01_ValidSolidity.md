# L01 ValidSolidity

## Purpose

`ValidSolidity` is valid, resolved Solidity. It is still a Solidity language,
not a compiler IR. Its job is to make source-language facts explicit enough that
the next pass does not repeat front-end reasoning.

The layer should contain only facts that later passes genuinely need. It should
not become an annotation warehouse.

## Change From Previous Layer

Compared with `SourceSolidity`, this layer removes ambiguity and invalidity:

- every identifier use resolves to a source identity;
- every overloaded call resolves to one declaration;
- every expression and lvalue has a type;
- every modifier, inheritance edge, override, and `super` use is legal;
- every call satisfies visibility, mutability, payability, and data-location
  rules;
- the program is inside the current verified fragment.

It does not remove Solidity constructs. Modifiers, `for`, short-circuit
operators, ternaries, destructuring, compound assignments, and high-level calls
may still appear here.

## Basic Syntax

The syntax should remain close to Solidity:

- contract declarations with resolved base-contract references;
- function, constructor, fallback, receive, modifier, event, error, and storage
  declarations;
- statements and expressions largely as in source;
- resolved source identities for locals, parameters, functions, modifiers,
  events, errors, storage declarations, structs, enum constructors, and builtins;
- type information available either as fields on nodes or as proof/evidence
  attached to the artifact.

Important source identities:

```text
LocalId
StorageDeclId
FunctionId
ModifierId
EventId
ErrorId
ContractId
StructId
```

These are source identities only. They are not ABI selectors, event topics,
storage slots, memory offsets, or bytecode labels.

## Semantics

`ValidSolidity` should usually reuse source semantics, with names and overloads
already resolved. If the implementation defines a separate evaluator, it should
be obviously equivalent to source evaluation under the checker theorem.

This layer still has Solidity behavior:

- source values and source types;
- source-level storage declarations, not concrete slots;
- source calls and modifiers;
- source return/revert/break/continue behavior;
- source checked/unchecked arithmetic.

## Incoming Pass: SourceSolidity -> ValidSolidity

The pass into this layer is checker/resolver/typechecker. It should do only
source-language work.

Transformations and checks:

- raw identifier names become resolved source identities;
- overloaded function, event, error, and modifier references become unique
  declarations;
- member lookup and `super` resolution are fixed according to Solidity rules;
- literal typing and implicit conversion checks are discharged;
- lvalues are classified as assignable or rejected;
- function bodies are checked against return types and mutability rules;
- `payable`, `view`, `pure`, `external`, `public`, `internal`, and `private`
  constraints are enforced;
- unsupported but syntactically valid features are rejected by the verified
  fragment predicate.

Non-transformations:

- do not expand modifiers;
- do not rewrite loops;
- do not normalize high-level calls into ABI calls;
- do not compute selectors, topics, storage slots, calldata offsets, or memory
  layouts.

The pass theorem should be an AST-level checker soundness theorem:

```text
check source = ok valid
  implies ValidWF valid
  and valid behavior matches source behavior.
```

## Outgoing Pass: ValidSolidity -> AbstractYul

The next pass is the first real compiler lowering. It consumes resolved Solidity
and handles source constructs directly:

- modifier semantics;
- short-circuit and ternary evaluation;
- compound assignment and increment/decrement result behavior;
- high-level internal and external calls;
- checked arithmetic;
- loop control, including `for` and `continue`;
- source returns, reverts, and fallthrough.

This layer should provide the source facts needed for that lowering without
precomputing compiler decisions that belong later.
