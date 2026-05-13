# SolidCore

`SolidCore` is the public Solidity semantics side of the project. The root
module imports `SolidCore.Spine`, which now exposes the source Solidity surface
and source-language typechecker only.

`Solidity/` contains reusable source-language executable semantics and ABI
support. `Spine/L00_SourceSolidity/` contains the canonical source AST,
source-level semantics, and typechecking surface. The former compiler pipeline
layers have been removed from this branch.
