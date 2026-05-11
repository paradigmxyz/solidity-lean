# L05 StackCfg

## Purpose

`StackCfg` is the first stack-machine-oriented language. It removes Yul lexical
structure and replaces it with explicit blocks, labels, stack effects, and
branch targets.

This layer exists because stack depth and control-flow graph obligations are a
different proof problem from Yul semantics and from byte encoding.

## Language Shape

Expected artifacts:

- labeled basic blocks;
- CFG edges and branch targets;
- stack-machine instructions or pseudo-instructions;
- explicit stack inputs and outputs for blocks;
- depth environment;
- layout of generated temporaries into stack/frame slots if needed;
- structured metadata connecting blocks to generated Yul origins when useful for
  proof.

No source lexical variables should remain. No concrete byte offsets are required
yet.

## Semantics

The semantics should be an abstract stack-machine step relation or block
execution relation:

- stack, memory, storage, calldata, returndata, logs, and environment as needed;
- branches by labels rather than byte offsets;
- pseudo-instructions allowed if they have clear lowering obligations;
- no byte encoding details.

## Wellformedness Boundary

This layer should own:

- labels are closed and unique;
- the entry label is defined;
- stack depth is known at every program point;
- block stack effects are consistent;
- branch targets have compatible stack shapes;
- branch targets and call targets are closed;
- no underflow or unsupported stack growth;
- max stack depth is within the EVM limit;
- terminal instructions occur only at block ends;
- pseudo-instructions are either explicitly interpreted here or marked for
  elimination before bytecode;
- generated labels are fresh and disjoint from any imported labels;
- generated temporary/frame discipline is respected.

Depth checking alone is not enough for backend soundness. A real program
wellformedness predicate should combine depth safety with label closure,
successor layout compatibility, block terminal discipline, and pseudo-instruction
elimination obligations.

## Outgoing Pass

`StackCfg -> Bytecode` resolves labels to byte offsets and encodes instructions.

The theorem should say that bytecode execution follows the same behavior as the
CFG, usually with a program-counter correspondence and jumpdest adequacy facts.
