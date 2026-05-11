# L05 Bytecode

## Purpose

`Bytecode` is the resolved executable artifact before target execution. It
separates byte encoding and jump resolution from both CFG reasoning and full EVM
world semantics.

## Change From Previous Layer

Compared with `StackCfg`, this layer:

- replaces labels with concrete program counters;
- linearizes blocks;
- chooses concrete PUSH widths;
- encodes opcodes and immediate bytes;
- proves jumps target `JUMPDEST`;
- proves no jump enters a PUSH immediate;
- eliminates all pseudo-instructions.

It is close to EVM execution, but it should not become a compiler-shaped
alternate EVM.

## Basic Syntax

Expected artifacts:

- byte array;
- optional decoded opcode view;
- program-counter map;
- label-to-PC map from the CFG;
- jumpdest set;
- runtime/deployment package metadata when constructors or initcode enter the
  theorem;
- `WF` certificate for resolved bytecode.

Representative structure:

```text
BytecodeArtifact:
  bytes : Bytes
  decoded : Pc -> Option OpcodeView
  entryPc : Pc
  labelPc : Label -> Pc
  jumpdests : Set Pc
  wf : Bytecode.WF bytes
```

## Semantics

This layer may expose a proof-convenient bytecode step relation, but any such
relation must have an adequacy theorem to the public `Evm` semantics.

The main semantics concern is artifact adequacy:

- bytes decode as intended;
- program counters advance by correct instruction lengths;
- jumps land on valid `JUMPDEST`s;
- invalid bytecode behavior is either visible or ruled out by `WF`.

## Incoming Pass: StackCfg -> Bytecode

This pass performs assembly and label resolution.

Transformations:

- choose a block order;
- insert `JUMPDEST`s;
- encode instructions;
- choose PUSH widths and immediate bytes;
- compute instruction lengths;
- compute label-to-PC map;
- replace label references with concrete PCs;
- remove all pseudo-instructions;
- package runtime/deployment bytes if needed.

Proof obligations:

- label-to-PC map is total for all CFG labels;
- label-to-PC map points to `JUMPDEST`;
- no jump target points into immediate bytes;
- code offsets are stable after PUSH-width selection;
- entry PC corresponds to CFG entry;
- every decoded instruction matches the source CFG instruction after resolution;
- inherited stack-safety facts still apply to the opcode stream.

The preservation theorem should establish a PC correspondence:

```text
resolve cfg = ok code
  and StackCfg.WF cfg
  imply Bytecode.WF code
  and bytecode execution from pc(label)
      refines StackCfg execution from label.
```

## Outgoing Pass: Bytecode -> Evm

The next step is target embedding: load the bytecode into the public EVM state
and run the public EVM semantics.
