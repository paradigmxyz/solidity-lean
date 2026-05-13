# Solid Core Architecture

This repository is now focused on the Solidity source language itself. The
public surface is the Solidity 0.8.x source AST, executable source semantics,
and source-language typechecking/modeling facts. Parser success, compiler
lowering, generated Yul, bytecode, and EVM execution are not public proof
targets on this branch.

## Public Shape

```text
Solidity source AST
  -> source typechecking and source-language validity
  -> executable source semantics
  -> source observations: returns, reverts, events, storage, calls, errors
```

The source semantics should model Solidity behavior directly: contracts,
inheritance, modifiers, dispatch, expressions, statements, storage and data
locations, checked and unchecked arithmetic, ABI-facing source behavior, events,
errors, try/catch, library behavior, payable behavior, and rollback on revert.

## External Semantics

When Solidity behavior is a wrapper over Yul/EVM behavior, the source model
should use shared imported primitives rather than reimplementing them locally.
The external reference is Nethermind's `EVMYulLean` package:

```text
https://github.com/NethermindEth/EVMYulLean.git
047f63070309f436b66c61e276ab3b6d1169265a
```

It is checked out as the reference submodule at
`external/nethermind/EVMYulLean`.

Because upstream currently targets a different Lean toolchain, this branch keeps
a local `EvmYul.UInt256` compatibility module for the word primitive slice used
by Solidity source semantics. The source layer may adapt these EVM/Yul-shaped
primitives into local `Word`, byte, external-call, storage, and environment
APIs, but the adapter should remain small and named. External contracts and the
host world may still be represented by explicit `External` records/oracles at
the Solidity layer.

## Layout

`SolidCore/Solidity/` contains reusable executable source semantics, ABI helpers,
Keccak support, and control-core views.

`SolidCore/Spine/L00_SourceSolidity/Interface.lean` is the canonical source
layer surface. Supporting source files, such as `TypeCheck.lean`, live beside it
when the implementation is too large for the interface file.

`SharedSemantics/` contains small cross-layer semantic foundations. It should
wrap EVM/Yul primitives for word-level and host-facing behavior instead of
growing a second EVM model.

## Removed Scope

The former compiler spine is intentionally removed from this branch:
ValidSolidity, AbstractYul, GeneratedYul, StackCfg, Bytecode, MeteredEvm, pass
interfaces, public compiler claims, and local EVM parity harnesses. Reintroduce
compiler artifacts only after the Solidity source semantics has a stable public
contract and only on a branch whose goal is compiler verification again.
