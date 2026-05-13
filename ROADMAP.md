# Roadmap

## Public Yul-To-EVM Spine

checked Yul fragment -> structured Yul IR -> stack CFG -> labeled EVM
assembly -> bytecode -> metered EVM target

The replacement route is built beside the current Solidity-to-EVM spine until
the theorem-bearing path is strong enough to become the public route.

## Layer Contract

- [ ] Every public Yul-to-EVM layer has syntax, semantics or relation,
      wellformedness, and a small interface module.
- [ ] Accepted-input checking is independent of compiler success.
- [ ] Gas-observing Yul is rejected until source and target gas semantics are
      aligned.
- [ ] Nethermind EVM/Yul semantics are preserved behind adapters rather than
      modified for proof convenience.

## Pass Contract

- [ ] Every pass imports only adjacent layer interfaces and shared foundations.
- [ ] Every pass defines a compiler function, wellformedness evidence, and a
      preservation theorem.
- [ ] Public claims compose adjacent pass theorems only.
- [ ] Bytecode claims reach the executable metered EVM target.

## Milestones

- [ ] Pin and integrate the Nethermind semantics boundary.
- [x] First expression-to-stack theorem for literals and pure word operations.
- [x] Variables and `let` with an explicit stack-layout relation.
- [ ] Memory operations `mload` and `mstore` with a memory relation.
- [x] Structured blocks and sequencing.
- [ ] `if` and `switch` through continuation labels.
- [ ] `for`, `break`, `continue`, and `leave` through explicit continuations.
- [ ] Internal functions, initially by inlining or a proved call discipline.
- [ ] Stack CFG to labeled EVM assembly simulation.
- [ ] Label resolution and bytecode offset correctness.
- [ ] Final accepted-fragment theorem from checked Yul AST to metered EVM.
- [ ] Optional parser/certificate ingestion after the AST theorem is stable.
