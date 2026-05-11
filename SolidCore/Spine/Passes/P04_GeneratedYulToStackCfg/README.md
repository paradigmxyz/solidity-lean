# P04 GeneratedYul To StackCfg

This pass lowers generated Yul into a stack-machine CFG with explicit labels and
stack-layout obligations.

The authoritative interface is `Interface.lean`; architectural intent lives in
`ARCHITECTURE.md`.
