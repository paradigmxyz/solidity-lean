# Spine

This folder is the public verified-compiler spine:

```text
L00_SourceSolidity
  -> L01_ValidSolidity
  -> L02_AbstractYul
  -> L03_GeneratedYul
  -> L04_StackCfg
  -> L05_Bytecode
  -> L06_Evm            # shared External EVM boundary
  -> L07_MeteredEvm     # exact executable metered EVM
```

Each `LNN_*` folder exposes one layer interface. `Passes/` contains the adjacent
compiler pass interfaces. `PublicClaims.lean` is where composed theorem claims
should live.

Each layer folder has a single `Interface.lean` file. That file is the
canonical language or artifact surface for the layer. The interfaces are still
scaffolding for the target architecture. When a placeholder fact becomes real,
strengthen the layer or pass where that fact is owned instead of adding a side
route.
