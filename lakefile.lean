import Lake
open Lake DSL

package «solid-core-spine» where
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩
  ]

@[default_target]
lean_lib SharedSemantics where

lean_lib SolidCore where

lean_lib SolidCoreYulCore where

lean_exe evm_parity where
  root := `tests.evm.EvmParityCli
