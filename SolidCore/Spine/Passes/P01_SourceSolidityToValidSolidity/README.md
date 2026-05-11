# P01 SourceSolidity To ValidSolidity

This pass checks source ASTs into valid Solidity artifacts. It owns checker
success, checker soundness, and accepted-input completeness at this boundary.

The authoritative interface is `Interface.lean`; architectural intent lives in
`ARCHITECTURE.md`.
