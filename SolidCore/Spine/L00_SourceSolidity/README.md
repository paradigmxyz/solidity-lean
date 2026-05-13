# L00 SourceSolidity

This layer exposes the source Solidity AST and source semantics used by the
public spine. It should describe source behavior directly, without compiler
lowering as the organizing principle.

`Interface.lean` is the canonical source-layer surface.

`TypeCheck.lean` contains the executable Solidity source typechecker. It remains
part of the source layer rather than a compiler pass.
