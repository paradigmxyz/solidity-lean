import Lake
open Lake DSL

package «solid-core-yulcore» where

@[default_target]
lean_lib SolidCoreYulCore where

@[default_target]
lean_exe evm_parity where
  root := `SolidCoreYulCore.BytecodeParityCli
