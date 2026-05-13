# Tests

This directory holds executable evidence and regression suites for the Solidity
source semantics. Tests support the Lean semantics, but they do not replace the
source-language definitions under `SolidCore.Spine.L00_SourceSolidity`.

## Layout

- `cases/`: shared semantic cases for source-interpreter replay.
- `solidity-interpreter/`: future source-layer replay for shared cases.
- `e2e-proofs/`: reserved for source-semantics claims and audits.

## Rule

Concrete tests may be specific. Source semantics code should stay recursive and
general; if a case exposes a missing rule, add the source-language rule or
record the unsupported Solidity behavior explicitly.
