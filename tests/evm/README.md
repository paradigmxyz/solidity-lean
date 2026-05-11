# EVM Tests

This folder holds executable evidence for the public EVM model. The Lean module
`EvmParityCli.lean` is the CLI used by the Forge harness.

`forge-parity/` compares Foundry execution with the Lean EVM model on selected
bytecode cases and replay scenarios. These tests are fidelity evidence for
`L06_Evm`; they are not a substitute for compiler correctness theorems.
