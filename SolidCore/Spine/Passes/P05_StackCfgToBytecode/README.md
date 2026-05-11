# P05 StackCfg To Bytecode

This pass assembles StackCfg programs into bytecode artifacts, resolving labels,
PCs, immediates, and jump destinations.

The authoritative interface is `Interface.lean`; architectural intent lives in
`ARCHITECTURE.md`.
