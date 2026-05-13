# L06 Evm

This layer exposes the proof-facing EVM boundary reached from L05 bytecode.
It routes external behavior through `SharedSemantics.External` so source,
intermediate, and bytecode layers can preserve the same external boundary.

`Interface.lean` is the canonical EVM-target-layer surface.
