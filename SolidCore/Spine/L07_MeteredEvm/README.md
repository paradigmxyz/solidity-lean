# L07 Metered Evm

This layer exposes the exact executable metered bytecode EVM used by the Forge
parity harness. It is intentionally below L06: compiler preservation should
first target the shared External boundary, then relate that boundary to
the exact runner when the theorem needs full EVM fidelity.
