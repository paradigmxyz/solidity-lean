import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "b08573c65e33feb5331abe2b7c1d76be89bb8eff"

-- The shared "language of composition": the interaction monad, Query/Answer,
-- OpenWorld, and ForwardRel, extracted verbatim from evm-compiler. Consumed as a
-- Lake path dependency (a sibling git repo); promote to a git URL later. A
-- hash-check (scripts/check_shared_interaction_hashes.py) guarantees its
-- Simulation sources stay byte-identical to evm-compiler's.
require «evm-interaction» from git
  "https://github.com/danrobinson/evm-interaction.git" @ "c939817c55f966dab97e1ba8df05ceca1fdfbdb2"

package «solidity-lean» where
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩
  ]

-- Single library. The former `SharedSemantics` EVM-primitive library is folded
-- in under `SolidCore/Solidity/Shared/` and builds transitively from this root.
@[default_target]
lean_lib SolidCore where

/-- Byte-parity witness for the repo-owned pure Keccak vs the pinned FFI hash.
    `supportInterpreter` + the transitively-linked `libleanffi` let the native
    pinned `keccak256` be compared against the pure implementation. -/
lean_exe keccakParity where
  root := `KeccakParity
  supportInterpreter := true

/-- Byte-parity witness for the in-semantics precompile implementations
    (`Precompile.execute?` / `Shared.Crypto`): sha256 and blake2f against the
    pinned NATIVE FFI, the rest against published known-answer vectors. -/
lean_exe precompileParity where
  root := `PrecompileParity
  supportInterpreter := true
