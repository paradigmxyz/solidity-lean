# P02 ValidSolidity To AbstractYul

This pass performs source-language lowering into AbstractYul. It is where
modifiers, short-circuiting, loop control, high-level calls, checked arithmetic,
and completions stop being Solidity surface constructs.

The authoritative interface is `Interface.lean`; architectural intent lives in
`ARCHITECTURE.md`.
