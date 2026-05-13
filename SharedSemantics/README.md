# SharedSemantics

This top-level folder owns pure semantic foundations that can be imported across
source, Yul, CFG, bytecode, and EVM layers without pulling in stack, memory, gas,
world state, or host-call machinery.

`Word.lean` defines the shared 256-bit word domain and pure word operations.
Layer-specific behavior such as Solidity checked arithmetic panics, EVM stack
effects, gas accounting, and memory/storage state remains in the layer that owns
that behavior.
