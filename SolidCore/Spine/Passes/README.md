# Passes

This folder contains one public pass for each adjacent spine edge:

```text
P01_SourceSolidityToValidSolidity
P02_ValidSolidityToAbstractYul
P03_AbstractYulToGeneratedYul
P04_GeneratedYulToStackCfg
P05_StackCfgToBytecode
P06_BytecodeToEvm
```

Each pass owns its compiler or checker function, success soundness, and any
accepted-input completeness theorem that belongs at that boundary. A pass should
import only adjacent layer interfaces plus shared foundations.

P06 targets the L06 shared External EVM boundary. Exact metered bytecode
execution lives below that boundary in L07.
