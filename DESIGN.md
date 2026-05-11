# Solid Core Top-Down Design

This document describes the target compiler spine we want to try next. The
current Lean code is still transitional; this is the design pressure for the
next refactor, not a claim that every folder already has this shape.

## Final Theorem Shape

The project is aiming for an AST-level theorem:

```text
for every valid Solidity source AST in the accepted fragment,
if the recursive compiler pipeline produces bytecode,
then running that bytecode in the public EVM semantics has behavior compatible
with the Solidity source semantics.
```

Tests, Forge parity, fuzzing, external parsers, and certificates are evidence.
They are not the public verification boundary until each has its own Lean
soundness theorem.

## Target Spine

```text
L00_SourceSolidity
  -> L01_ValidSolidity
  -> L02_AbstractYul
  -> L03_GeneratedYul
  -> L04_StackCfg
  -> L05_Bytecode
  -> L06_Evm
```

The main simplification from the previous design is that there is no separate
public `CheckedSolidity`/`DesugaredSolidity` pair. The checker creates
`ValidSolidity`, and the first real lowering pass goes directly from
`ValidSolidity` to `AbstractYul`.

## Cross-Cutting Rules

- Each layer needs direct semantics or direct artifact invariants.
- No layer's semantics should be defined by compiling it to the next layer.
- No layer's wellformedness should mean "the next pass succeeds."
- Parser success, source validity, compiler success, and certificate checking
  are separate facts.
- Assumptions for ABI, storage layout, hashing, logs, external calls, gas, fuel,
  and host behavior must be named in artifacts, profiles, or theorem hypotheses.
- Fixture/story routes should stay out of the public theorem spine.

## Layer Docs

The detailed layer/pass design now lives in:

- [L00 SourceSolidity](./docs/languages/L00_SourceSolidity.md)
- [L01 ValidSolidity](./docs/languages/L01_ValidSolidity.md)
- [L02 AbstractYul](./docs/languages/L02_AbstractYul.md)
- [L03 GeneratedYul](./docs/languages/L03_GeneratedYul.md)
- [L04 StackCfg](./docs/languages/L04_StackCfg.md)
- [L05 Bytecode](./docs/languages/L05_Bytecode.md)
- [L06 Evm](./docs/languages/L06_Evm.md)

Each doc describes the layer syntax, the change from the previous layer, and
the compiler pass that produces it.

## Current Design Bet

`ValidSolidity` should be source-validity only: resolution, typechecking,
inheritance legality, overload resolution, mutability/payability checks, and
accepted-fragment membership. It should not compute storage slots, selectors,
event topics, ABI offsets, memory layout, or Yul-like control.

`AbstractYul` should absorb the source-to-IR work we briefly considered putting
in a public desugaring layer: modifiers, short-circuiting, ternaries, compound
assignments, high-level calls, loop control, completions, checked arithmetic,
returns, reverts, and typed abstract effects.

That keeps the spine shorter and makes each layer earn its keep.
