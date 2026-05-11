# Language Spine

These docs describe the target language spine we want to design toward. The
current Lean code is still transitional; the docs are intentionally ahead of the
implementation where the architecture has become clearer.

Target spine:

```text
L00_Source
  -> L01_CheckedSolidity
  -> L02_DesugaredSolidity
  -> L03_AbstractYul
  -> L04_GeneratedYul
  -> L05_StackCfg
  -> L06_Bytecode
  -> L07_Evm
```

The core idea is to avoid thin layers. Each language must change the proof
problem in a visible way:

- Solidity richness is checked and simplified before Yul-shaped lowering.
- `AbstractYul` introduces Yul-like scope/control while effects remain typed and
  abstract.
- `GeneratedYul` is concrete enough to talk about Yul builtins and layout.
- `StackCfg`, `Bytecode`, and `Evm` separate stack invariants, byte encoding, and
  target execution.

Two cross-cutting constraints from earlier oracle review apply to every layer:

- The public theorem spine should be AST/semantics-shaped. Parser success,
  certificate checking, fixture recognition, and external parity tests are
  separate evidence paths, not the compiler correctness theorem itself.
- Each layer should have direct semantics or a direct artifact invariant. Do not
  define a layer's behavior by compiling it to the next layer, and do not make
  wellformedness mean "the next pass succeeds."

Layer docs:

- [L00 Source](./L00_Source.md)
- [L01 CheckedSolidity](./L01_CheckedSolidity.md)
- [L02 DesugaredSolidity](./L02_DesugaredSolidity.md)
- [L03 AbstractYul](./L03_AbstractYul.md)
- [L04 GeneratedYul](./L04_GeneratedYul.md)
- [L05 StackCfg](./L05_StackCfg.md)
- [L06 Bytecode](./L06_Bytecode.md)
- [L07 Evm](./L07_Evm.md)
- [Sample Vault Walkthrough](./SAMPLE_VAULT_WALKTHROUGH.md)
- [Critique](./CRITIQUE.md)
