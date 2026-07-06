import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "3c5c44a62f4e7964bd1bc648caa708a111664c84"

-- The shared "language of composition": the interaction monad, Query/Answer,
-- OpenWorld, and ForwardRel, extracted verbatim from evm-compiler. Consumed as a
-- Lake path dependency (a sibling git repo); promote to a git URL later. A
-- hash-check (scripts/check_shared_interaction_hashes.py) guarantees its
-- Simulation sources stay byte-identical to evm-compiler's.
require «evm-interaction» from ".." / "evm-interaction"

package «solid-core-spine» where
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩
  ]

@[default_target]
lean_lib SharedSemantics where

lean_lib SolidCore where

/-- Byte-parity witness for the repo-owned pure Keccak vs the pinned FFI hash.
    `supportInterpreter` + the transitively-linked `libleanffi` let the native
    pinned `keccak256` be compared against the pure implementation. -/
lean_exe keccakParity where
  root := `KeccakParity
  supportInterpreter := true
