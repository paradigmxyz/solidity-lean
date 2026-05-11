# Solid Core Top-Down Design

This document describes the target compiler spine. The current Lean code is
still transitional in places; this file is the design pressure we should refactor
toward, not a claim that every folder already has this final shape.

## Final Theorem Shape

The project is aiming for an AST-level theorem:

```text
for every checked Solidity source AST,
if the recursive compiler pipeline produces bytecode,
then running that bytecode in the public EVM semantics has behavior compatible
with the Solidity source semantics.
```

Tests, Forge parity, fuzzing, external parsers, and certificates are evidence.
They are not the public verification boundary until each has its own Lean
soundness theorem.

Target spine:

```text
L00_Source
  -> L01_CheckedSolidity
  -> L02_DesugaredSolidity
  -> L03_AbstractYul
  -> L04_GeneratedYul
  -> L05_StackCfg
  -> L06_Bytecode
  -> L07_Evm
```

## Cross-Cutting Rules

- Each layer needs direct semantics or direct artifact invariants.
- No layer's semantics should be defined by compiling it to the next layer.
- No layer's wellformedness should mean "the next pass succeeds."
- Parser success, accepted-source checking, compiler success, and certificate
  checking are separate facts.
- Assumptions for ABI, storage layout, hashing, logs, external calls, gas, fuel,
  and host behavior must be named in artifacts, profiles, or theorem hypotheses.
- Fixture/story routes should stay out of the public theorem spine.

## Layers And Passes

### L00_Source

Role: broad Solidity-facing AST and source semantics.

This layer owns user-visible constructs: contracts, functions, modifiers,
source expressions, statements, storage declarations, events, errors, inheritance
metadata, and Solidity-level runtime behavior. It should not assume names are
resolved, expressions are typed, modifiers are valid, storage layout is known, or
the program is inside the verified subset.

### P01_SourceToCheckedSolidity

Role: independent checker, resolver, and typechecker.

The pass should turn a source AST into a checked artifact. Its theorem should
say successful checking creates the static facts later passes rely on, without
mentioning later compiler success.

Key output facts:

- resolved identifiers and scopes;
- unique local handles rather than semantic reliance on bare strings;
- explicit storage identities or storage locations;
- function, modifier, event, error, and declaration identities;
- type facts for expressions, lvalues, calls, returns, and emitted data;
- supported-feature evidence.

### L01_CheckedSolidity

Role: checked Solidity artifact with evidence.

`CheckedSolidity` usually reuses source semantics. Its value is not a new
runtime model; its value is the static evidence that makes later compiler passes
honest.

The checked artifact should eventually contain no unresolved variable uses. A
bare name from source may remain as diagnostic metadata, but semantic identity
should be local handles, function ids, event ids, error ids, and storage ids.

### P02_CheckedSolidityToDesugaredSolidity

Role: source-to-source desugaring.

This pass removes Solidity surface structure while preserving source behavior.
It should handle features whose meaning is best explained once as a rewrite into
a smaller Solidity core.

Likely responsibilities:

- modifier expansion;
- inheritance and override choices after checking;
- constructors, fallback, and receive normalization where useful;
- tuple/destructuring and declaration sugar;
- implicit evaluation-order conveniences.

This pass should not introduce Yul-only constructs, storage slots, memory
offsets, or stack concepts.

### L02_DesugaredSolidity

Role: smaller Solidity core.

This layer is still Solidity-like. It keeps typed expressions, source-level
values, blocks, locals, returns, reverts, loops, conditionals, functions, and
storage/event/call concepts. It should be simpler than source, but not yet
Yul-shaped.

### P03_DesugaredSolidityToAbstractYul

Role: cross the source-to-IR boundary.

This pass changes the scoping and control model. Source lexical scopes become
generated Yul-like local bindings. Source statements and expressions become
explicit evaluation order, explicit exits, and typed abstract effects.

Function calls become explicit abstract call/evaluation behavior here, but
selector dispatch and ABI encoding do not. Solidity has no `switch`; generated
Yul dispatch belongs in the next pass.

### L03_AbstractYul

Role: Yul-shaped control and scoping with typed abstract effects.

This is the middle proof boundary. It owns Yul-like blocks, lets, assignment,
`if`, `switch`, loops, procedure-like structure if needed, generated names,
explicit returns/reverts, and typed abstract operations.

Example abstract effects:

```text
StorageRead(field, keys)
StorageWrite(field, keys, value)
Emit(eventId, typedArgs)
ExternalCall(target, selector, typedArgs, value)
Return(typedValues)
Revert(errorId, typedArgs)
```

It should not own concrete ABI head/tail offsets, memory pointer arithmetic,
storage slot formulas, concrete Yul builtins, stack depth, or byte offsets.

### P04_AbstractYulToGeneratedYul

Role: layout and concrete Yul generation.

This pass lowers typed abstract effects into the generated Yul subset. It is
where layout lives.

Responsibilities:

- storage locations become slot/hash formulas plus `sload`/`sstore`;
- typed returns/reverts become memory buffers plus `return`/`revert`;
- events become topics/data buffers plus `logN`;
- external calls become ABI-encoded calldata and concrete `call` variants;
- function dispatch can become Yul `switch`;
- ABI, storage, hashing, logs, host calls, and gas exclusions become named
  profile assumptions or theorem hypotheses.

### L04_GeneratedYul

Role: concrete generated Yul subset, not arbitrary Yul.

This layer owns Yul-style blocks, lets, assignments, ifs, switches, loops,
helper functions if emitted, and concrete builtins such as `mload`, `mstore`,
`calldataload`, `sload`, `sstore`, `keccak256`, `logN`, `call`, `return`, and
`revert` as they enter scope.

It should define a generated-subset `WF` early. The goal is not to validate all
Yul; the goal is to prove the Yul we generate.

### P05_GeneratedYulToStackCfg

Role: structured low-level code to stack CFG.

This pass lowers generated Yul into labeled blocks with explicit stack effects,
branch targets, and stack layouts. Its theorem should say CFG execution refines
generated Yul execution.

Responsibilities:

- expression-to-stack correctness;
- local convention correctness;
- block stack signatures;
- join compatibility;
- no underflow;
- max stack depth within the EVM limit;
- branch target closure.

### L05_StackCfg

Role: stack-oriented control-flow graph.

This layer owns labels, blocks, stack-machine instructions or pseudo-
instructions, stack inputs and outputs for blocks, branch targets, depth facts,
and generated-label discipline.

`DepthChecked` is not enough. The public backend boundary needs `Program.WF`
with label uniqueness, entry closure, branch and call target closure, stack
layout compatibility, terminal-at-end discipline, max-stack bounds, generated
label freshness, and pseudo-instruction elimination obligations.

### P06_StackCfgToBytecode

Role: label resolution and byte encoding.

This pass linearizes CFG blocks, resolves labels to program counters, eliminates
pseudo-instructions, and emits bytecode. Its theorem should establish a
program-counter correspondence between CFG labels and bytecode execution.

Responsibilities:

- label-to-PC map totality for all labels;
- jumps land on `JUMPDEST`;
- no jumps into PUSH immediate bytes;
- PUSH widths and instruction lengths are correct;
- entry PC matches CFG entry;
- unresolved labels and pseudo-instructions are gone.

### L06_Bytecode

Role: resolved bytecode artifact before target execution.

This layer owns bytes, decoded opcode views if useful, immediate bytes,
jumpdest maps, deployment/runtime packaging if needed, and adequacy facts that
connect the byte array to the intended instructions.

It should not become an alternate EVM. If it exposes proof-convenient execution,
that execution needs an adequacy theorem to the public EVM semantics.

### P07_BytecodeToEvm

Role: target embedding, not real compilation.

This pass packages resolved bytecode into the public EVM model: account code,
initial call frame, calldata, gas assumptions, world state, and environmental
relations.

The theorem should say the public EVM execution of the bytecode refines the
bytecode artifact semantics, or directly supplies the final target behavior.

### L07_Evm

Role: final target semantics.

This layer owns opcode execution, stack, memory, storage, accounts, calls,
return/revert/stop/failure behavior, logs, gas where claimed, deployment where
claimed, and external host/precompile behavior where claimed.

The EVM model should not be shaped around compiler convenience. Early claims may
be gasless, single-contract, or external-call-free, but those restrictions must
be explicit in profiles or accepted-subset facts.

## Layer-Fit Critique

This target spine looks ready for detailed design work.

The strongest design choice is `AbstractYul -> GeneratedYul`: it replaces the
older vague `Control/Effect/Layout` split with one clear boundary between
Yul-shaped abstract effects and concrete generated Yul with layout. That is the
place where dispatch-to-switch, ABI encoding, storage slot formulas, log
payloads, return/revert buffers, and external call lowering belong.

The main risk is that `AbstractYul` becomes too large. If it grows into a
general effect calculus with half of Solidity inside it, the pass to
`GeneratedYul` will be as hard as the whole compiler. Keep it Yul-shaped and add
abstract effects only when the next verified slice needs them.

The second risk is underpowered backend WF. Stack depth, by itself, cannot
justify bytecode lowering. The backend theorem needs full `StackCfg.Program.WF`
and bytecode resolution correctness before any EVM correctness claim should be
advertised.

The third risk is a text/certificate theorem pretending to be compiler
correctness. The first public theorem should stay AST-level until parser and
certificate soundness are proved separately.

## First Slice

The next design validation should be a tiny recursive slice:

```text
checked local variable + arithmetic + return
  -> desugared Solidity core
  -> AbstractYul lets and return effect
  -> GeneratedYul memory return convention
  -> StackCfg
  -> Bytecode
  -> gasless EVM return behavior
```

If that slice makes `AbstractYul` feel like a thin wrapper, collapse it. If it
forces concrete ABI/storage/memory details into `AbstractYul`, constrain the
layer harder and keep those details in `P04_AbstractYulToGeneratedYul`.
