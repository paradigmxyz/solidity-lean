# Roadmap

## Solidity Source Semantics

- [x] Keep `L00_SourceSolidity/Interface.lean` as the canonical source surface.
- [x] Move source typechecking out of the compiler pass namespace.
- [x] Remove the local compiler-pipeline attempt from this branch.
- [x] Add Nethermind `EVMYulLean` as a pinned reference submodule under
      `external/nethermind/EVMYulLean`.
- [x] Add an `EvmYul.UInt256` compatibility surface for the Nethermind word
      primitive API used by the source semantics.
- [x] Route word-level Solidity wrappers through the shared `EvmYul.UInt256`
      adapter.
- [ ] Route environment/storage/log/call wrappers through named shared adapters
      where Nethermind exposes the matching primitive.
- [ ] Finish source typechecking coverage for Solidity 0.8.35 features.
- [ ] Finish executable source semantics for try/catch, libraries, payable,
      inheritance dispatch, modifiers, rollback, events, errors, and data
      locations.
- [ ] Add small executable source examples for each supported Solidity feature.
- [ ] Record unsupported Solidity behavior explicitly until modeled.

## Boundary Rules

- Parser/import success is not source semantics unless separately verified.
- Compiler convenience must not shape Solidity semantics.
- External contracts and host behavior may remain explicit `External` oracle
  records at the Solidity layer.
- Shared primitive behavior should be imported through named modules when
  Solidity is simply exposing Yul/EVM behavior.
