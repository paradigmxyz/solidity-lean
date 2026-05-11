import Lake
open Lake DSL

package «solid-core-spine» where

@[default_target]
lean_lib SolidCore where

lean_lib SolidCoreYulCore where

lean_exe evm_parity where
  root := `tests.evm.EvmParityCli
