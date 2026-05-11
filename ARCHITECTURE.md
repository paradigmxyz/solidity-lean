# Solid Core Architecture

This repository is a Lean-first verified compiler spine for Solidity-like
source programs down to an EVM model. The public claim should always be stated
through the spine below, not through parser success, fixtures, examples, parity
tests, or compatibility paths.

## Public Theorem Shape

```text
For every source Solidity AST accepted by the validity layer,
if each adjacent compiler pass succeeds through bytecode,
then running the resulting bytecode in the public EVM semantics
matches the source semantics under the theorem's named assumptions.
```

Parser ingestion, certificate checking, Forge parity, fuzzing, and corpus replay
are useful evidence. They are not part of the verified claim until Lean has a
theorem connecting them to the same source semantics and target interpreter.

## Spine

```text
L00_SourceSolidity
  -> L01_ValidSolidity
  -> L02_AbstractYul
  -> L03_GeneratedYul
  -> L04_StackCfg
  -> L05_Bytecode
  -> L06_Evm
```

Every public pass is adjacent. No public compiler path should skip a layer.
Every layer should have either direct semantics or direct artifact invariants;
no layer's meaning should be "whatever the next compiler pass does."

Each layer folder has a `Syntax.lean` module for the proposed AST/artifact
syntax and an `Interface.lean` module for the currently imported public surface.

## Layers And Passes

`L00_SourceSolidity` is the broad source AST and source semantics. It represents
Solidity constructs before validity checking: functions, modifiers, expressions,
locals, storage references, events, errors, calls, returns, reverts, break,
continue, and checked/unchecked arithmetic. Parser success is outside this
layer unless separately verified.

`P01_SourceSolidityToValidSolidity` checks source validity. It owns fragment
membership, name/scope resolution, overload resolution, typechecking, lvalue
legality, inheritance and override legality, mutability/payability checks,
modifier legality, and related source-language facts.

`L01_ValidSolidity` is valid Solidity, not a compiler IR. It may carry stable
source identities and facts needed by multiple later proofs. It must not carry
selectors, event topics, concrete storage slots, ABI offsets, memory layout,
stack plans, byte offsets, or EVM conveniences.

`P02_ValidSolidityToAbstractYul` is the source-language lowering pass. It handles
modifier behavior, short-circuiting, ternaries, compound assignments, loop
control, high-level calls, checked arithmetic, return/revert/fallthrough
completions, and source effects. This pass may use internal helpers, but it
should not create a new public layer unless the whole spine is deliberately
revised.

`L02_AbstractYul` is Yul-shaped control with generated locals, scopes, procedures,
explicit completions, and typed abstract effects. Storage, events, errors,
external calls, environment reads, returns, reverts, and rollback behavior are
modeled abstractly here. Concrete ABI, slot, topic, memory, and builtin details
belong later.

`P03_AbstractYulToGeneratedYul` concretizes abstract effects and entries into the
generated Yul profile. It introduces selector dispatch, calldata decoding, return
and revert encoding, storage layout, mapping hash formulas, event topics and
data encoding, panic/custom-error encoding, memory discipline, and concrete
helpers or builtins emitted by the compiler.

`L03_GeneratedYul` is the concrete generated Yul subset. It is not a commitment
to support arbitrary user-written Yul. Its profile should be justified by what
the compiler emits.

`P04_GeneratedYulToStackCfg` lowers generated Yul into a stack-machine control
flow graph. It owns stack planning, block signatures, labels, branch/call
targets, and the proof that generated Yul behavior is preserved by the CFG.

`L04_StackCfg` is a label-based CFG with stack effects and wellformedness. It
should know about labels, successors, stack depths, underflow, `DUP`/`SWAP`
validity, terminal instructions, and max stack limits. It should not know byte
offsets or final `PUSH` widths.

`P05_StackCfgToBytecode` assembles and resolves the CFG. It owns linearization,
label-to-PC maps, opcode/immediate encoding, `JUMPDEST` adequacy, no jumps into
immediates, and bytecode-level preservation of CFG execution.

`L05_Bytecode` is the byte artifact and any decoded view needed for proofs. It
does not own account/world semantics; those are EVM concerns.

`P06_BytecodeToEvm` connects bytecode artifacts to the public EVM semantics. It
states the boundary conditions under which bytecode execution corresponds to
the artifact-level semantics.

`L06_Evm` is the target model. It owns opcode execution, stack, memory, storage,
logs, returndata, calls, frames, account/world state, gas/OOG, deployment,
precompiles, and host assumptions as they enter scope. Forge parity and replay
tests are evidence for fidelity, not proof by themselves.

## Invariants

- Accepted input is independent of compiler success.
- Compiler passes are recursive and structural, not fixture- or story-shaped.
- Public root imports cite the spine and reusable semantic foundations only.
- Assumptions live in theorem hypotheses, artifact fields, profiles, or code,
  not in free-floating prose.
- Tests may be concrete; compiler and semantics code should remain general.
- Obsolete routes should be deleted instead of kept as compatibility wrappers.

## Documentation Policy

This file is the single global architecture document. Folder-local `README.md`
files may explain what lives in that folder and how it participates in the
spine. Do not add separate scratch, critique, sample-walkthrough, design-history,
roadmap, or progress-log documents unless the project deliberately changes this
policy.
