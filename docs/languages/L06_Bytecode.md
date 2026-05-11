# L06 Bytecode

## Purpose

`Bytecode` is the resolved executable artifact before target execution.

It separates byte encoding and jump resolution from the EVM target semantics.
That keeps the EVM model from becoming compiler-shaped and keeps stack CFG
proofs from carrying byte-offset arithmetic too early.

## Language Shape

Expected artifacts:

- byte arrays;
- decoded opcode view if useful;
- immediate bytes;
- jumpdest map;
- proof/certificate that pseudo-instructions are gone;
- code-deployment or multi-contract metadata when the subset needs it.

## Semantics

This layer may expose a decoded step relation for proof convenience, but it
should not be an alternate EVM. Any executable semantics must be connected to
the public `Evm` semantics.

The main concern is adequacy of the artifact:

- bytes decode to intended opcodes;
- jumps land on valid `JUMPDEST`s;
- no jump into immediates;
- instruction lengths and program counters are correct.

## Wellformedness Boundary

This layer should own:

- valid byte encoding;
- resolved jump destinations;
- no unresolved pseudo-instructions;
- no malformed immediates;
- a total label-to-PC map for labels inherited from `StackCfg`;
- jump targets that land on `JUMPDEST`;
- no jumps into PUSH immediate bytes;
- instruction lengths and offsets stable after label resolution;
- an entry PC corresponding to the CFG entry label;
- stack-safety facts inherited from `StackCfg`;
- deployment/runtime-code separation if needed.

If the bytecode semantics has invalid or stuck states, they must remain visible
as outcomes or be ruled out by `Bytecode` wellformedness. They should not be
erased in a way that makes refinement vacuous.

## Outgoing Pass

`Bytecode -> Evm` is not really compilation. It is target adequacy: the final
byte array is executed by the public EVM semantics.

The theorem should mention the actual bytecode artifact and the public target
interpreter/relation.
