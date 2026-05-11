# Tests

This directory holds executable evidence and regression suites. Tests support
the verified compiler spine, but they do not define what is verified; Lean
theorems under `SolidCore.Spine` remain the public proof boundary.

## Layout

- `evm/forge-parity/`: Forge/Foundry parity harness for the Lean EVM model.
- `bin/`: harness runners used by Forge FFI and corpus replay.
- `cases/`: shared semantic cases. These should eventually drive EVM parity,
  source-interpreter replay, and end-to-end proof checks from the same inputs.
- `solidity-interpreter/`: future source-layer replay for shared cases.
- `e2e-proofs/`: future tests that named compiler claims cover shared cases
  through the declared target interpreter.

## Rule

Concrete tests may be specific. Compiler and semantics code should stay
recursive and general; if a case exposes a missing proof, add the generic
pass theorem or narrow the accepted subset.
