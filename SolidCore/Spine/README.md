# Spine

This folder is now the public Solidity source-semantics surface:

```text
L00_SourceSolidity
```

`L00_SourceSolidity/Interface.lean` is the canonical language surface. Supporting
source-language files such as `TypeCheck.lean` may live beside it when the
implementation is too large for a single file.

Compiler pass layers, generated Yul, stack CFG, bytecode, and local EVM
lowering attempts were removed on the semantics-only branch. Solidity behavior
that is merely a wrapper around Yul/EVM primitives should be routed through the
shared primitive adapters instead of reintroducing compiler scaffolding.
