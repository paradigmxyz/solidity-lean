import Lake
open Lake DSL

package «solid-core-spine» where
  leanOptions := #[
    ⟨`maxHeartbeats, 1000000⟩
  ]

@[default_target]
lean_lib EvmYul where

@[default_target]
lean_lib SharedSemantics where

lean_lib SolidCore where
