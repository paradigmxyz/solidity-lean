# Language Spine

These docs describe the target language spine we want to try next. The Lean
code is still transitional; these docs are the design to refactor toward.

Target spine:

```text
L00_SourceSolidity
  -> L01_ValidSolidity
  -> L02_AbstractYul
  -> L03_GeneratedYul
  -> L04_StackCfg
  -> L05_Bytecode
  -> L06_Evm
```

The design principle is that a layer exists only when it changes the proof
problem:

- `ValidSolidity` proves source-language validity and resolution, but carries no
  compiler layout facts.
- `AbstractYul` is the first real lowering layer: Yul-shaped control, explicit
  completions, and typed abstract effects.
- `GeneratedYul` is concrete generated Yul with ABI, storage layout, memory
  discipline, and builtins.
- `StackCfg`, `Bytecode`, and `Evm` separate stack invariants, byte encoding,
  and target execution.

Two constraints apply throughout:

- The public theorem spine should be AST/semantics-shaped. Parser success,
  certificate checking, fixture recognition, and external parity tests are
  separate evidence paths, not the compiler theorem.
- Each layer should have direct semantics or direct artifact invariants. Do not
  define a layer's behavior by compiling it to the next layer, and do not make
  wellformedness mean "the next pass succeeds."

Layer docs:

- [L00 SourceSolidity](./L00_SourceSolidity.md)
- [L01 ValidSolidity](./L01_ValidSolidity.md)
- [L02 AbstractYul](./L02_AbstractYul.md)
- [L03 GeneratedYul](./L03_GeneratedYul.md)
- [L04 StackCfg](./L04_StackCfg.md)
- [L05 Bytecode](./L05_Bytecode.md)
- [L06 Evm](./L06_Evm.md)
- [Sample Vault Walkthrough](./SAMPLE_VAULT_WALKTHROUGH.md)
- [Critique](./CRITIQUE.md)
