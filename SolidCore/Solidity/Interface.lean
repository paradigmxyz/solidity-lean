import SolidCore.Solidity.Interface.Contracts

/-! Compatibility import for the executable Solidity source semantics.

The declarations retain their original names and bodies. TypeCheck imports only
Foundation and ContractMetadata, so edits to expression/statement lowering do
not rebuild the typechecker. Import this module for the full lowering pipeline.
-/
