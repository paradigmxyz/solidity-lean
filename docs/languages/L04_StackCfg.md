# L04 StackCfg

## Purpose

`StackCfg` is a stack-machine control-flow graph. It removes Yul lexical binding
and structured control before byte encoding.

This layer exists because stack layout and CFG wellformedness are a different
proof problem from generated Yul semantics and byte-level EVM execution.

## Change From Previous Layer

Compared with `GeneratedYul`, this layer:

- replaces structured Yul blocks with labeled basic blocks;
- replaces Yul locals with stack positions, frame slots, or a verified local
  convention;
- replaces structured branches and switches with explicit label targets;
- replaces helper functions with CFG call/return conventions or inlined blocks;
- exposes stack inputs and outputs at every block boundary;
- tracks stack depth and join compatibility.

It still does not have byte offsets, PUSH widths, or concrete program counters.

## Basic Syntax

Expected artifact:

```text
Program:
  entry : Label
  blocks : Map Label Block

Block:
  inputLayout : StackLayout
  instrs : List Instr
  terminal : Terminal

Instr:
  push(value)
  dup(index)
  swap(index)
  pop
  builtin(op)
  mload/mstore/sload/sstore/log/call variants
  pseudo instructions if explicitly eliminated before bytecode

Terminal:
  jump(label)
  branch(cond, thenLabel, elseLabel)
  return(offset, size)
  revert(offset, size)
  stop
```

The pass may use an internal symbolic stack-planning notation with names. The
public `StackCfg` artifact should still prove positional stack effects.

## Semantics

The semantics should step by labels, not byte offsets:

- stack;
- memory;
- storage;
- calldata;
- returndata;
- logs;
- call environment as inherited from the generated Yul profile;
- label-directed control flow.

Pseudo-instructions may exist only if they have direct semantics here and an
explicit elimination theorem before bytecode.

## Incoming Pass: GeneratedYul -> StackCfg

This pass lowers structured generated Yul into stack CFG.

Transformations:

- translate expressions into stack-producing instruction sequences;
- allocate Yul locals into stack positions, frame slots, or a proven convention;
- translate `if` and `switch` into labels and branches;
- translate loops into labels and backedges;
- translate generated helper functions into CFG call conventions or inline
  blocks;
- plan `DUP`/`SWAP`/`POP` operations;
- remove or mark structured Yul constructs that cannot reach bytecode directly;
- compute block input and output stack layouts;
- compute depth environment.

The pass must produce real `Program.WF`, not just depth checking.

Required WF fields:

- labels are unique;
- entry label exists;
- branch targets are closed;
- call targets are closed if CFG calls exist;
- every block has the advertised input stack shape;
- successors agree with target stack layouts;
- terminal instructions occur only at block ends;
- no stack underflow;
- `DUP` and `SWAP` indices are valid;
- max stack is within the EVM limit;
- generated labels are fresh;
- pseudo-instructions are eliminated or explicitly marked for the next pass.

The preservation theorem should relate label-based CFG execution to generated
Yul execution.

## Outgoing Pass: StackCfg -> Bytecode

The next pass linearizes blocks, resolves labels to program counters, eliminates
remaining pseudo-instructions, and emits EVM bytecode.
