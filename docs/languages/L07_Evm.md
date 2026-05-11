# L07 Evm

## Purpose

`Evm` is the declared target semantics. It should model the EVM accurately
enough for the verified compiler claim and should not be shaped around the
compiler's convenience.

Forge parity tests are evidence for this layer. Lean theorem statements are the
verification boundary.

## Language Shape

The target language is EVM bytecode running in an EVM state:

- program counter;
- stack;
- memory;
- storage;
- calldata;
- returndata;
- logs;
- gas where modeled;
- account/code environment;
- call/create/precompile behavior as the model expands.

## Semantics

The semantics should be the public target relation used by final compiler
theorems.

It should cover:

- opcode execution;
- call-like opcodes;
- revert/return/stop/failure behavior;
- memory expansion and gas if included in the claim;
- logs and observable outputs;
- account/storage effects.

If a proof adapter is introduced, it must have an adequacy theorem back to this
public semantics.

The final public claim should make exclusions explicit. Early theorems may be
gasless, single-contract, or external-call-free, but those choices should appear
as profile assumptions or accepted-subset restrictions. Forge parity belongs as
test evidence for this target model, not as the proof boundary.

## Wellformedness Boundary

EVM itself accepts bytecode. Compiler-produced wellformedness facts mostly
belong to `Bytecode`. The target layer may still define predicates for valid
states, environmental assumptions, or execution fuel.

## Incoming Boundary

`Bytecode -> Evm` should assert that the resolved bytecode artifact is run by
this target model.

The final theorem should reach this layer, not stop at bytecode and not use an
unconnected adapter semantics.
