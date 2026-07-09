# Compile-to-Yul readiness (relocated)

Moved 2026-07-09, with all compiler planning, to
`../evm-compiler/docs/solidity-lowering/compile-to-yul-readiness.md`
(alongside `lowering-roadmap.md` and `memory-layer-design.md`).

This repo is the Solidity source semantics only; the lowering/compiler
project lives in `../evm-compiler`, which pins this repo as its source
language. Source-side prerequisites for the lowering (gap fixes, storage
encoding `E`, freeze) are tracked as Stage 0 of the roadmap there.
