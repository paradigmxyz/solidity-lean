# Critique Of Target Language Docs

This critique is local and provisional. Oracle review for the earlier
AbstractYul spine is still pending in conversation:

```text
20260511-190754-solid-core-abstractyul-spine-critique-6220c34f
```

The current docs move beyond that request by dropping the separate
`CheckedSolidity` and `DesugaredSolidity` public layers.

## Overall Readiness

The new target spine is:

```text
SourceSolidity
  -> ValidSolidity
  -> AbstractYul
  -> GeneratedYul
  -> StackCfg
  -> Bytecode
  -> Evm
```

This is cleaner than the previous design. It avoids a desugaring layer whose
only stable purpose was "maybe simple rewrites." Instead, source validity is one
front-end layer, and the first compiler pass goes straight into an IR designed
for explicit control and effects.

## Strong Points

- `ValidSolidity` now has a crisp job: source-language legality and resolution.
- No public layer exists merely to hold optional annotations.
- Modifier expansion, short-circuiting, ternaries, compound assignment, and
  loop-control compilation happen in one semantic lowering pass.
- `AbstractYul` remains the right place for explicit completions and typed
  abstract effects.
- `GeneratedYul` remains the boundary where selectors, topics, ABI buffers,
  storage slots, memory discipline, and concrete builtins appear.
- The lower layers remain crisp: stack CFG, bytecode, and EVM each own a
  different proof burden.

## Main Open Risks

### ValidSolidity Could Become Too Heavy

It should not become `CheckedSolidity` under a new name. If a fact is not needed
by more than one later proof, and recomputing it is not subtle, it probably does
not belong in the layer artifact.

Keep source identities and type facts. Avoid compiler facts such as selectors,
event topics, slot numbers, ABI offsets, memory layout, or stack plans.

### AbstractYul Is Now The Hard Pass

Dropping `DesugaredSolidity` is a good simplification, but it moves all source
surface compilation into `ValidSolidity -> AbstractYul`.

This pass must handle:

- modifier continuation behavior;
- short-circuit and ternary evaluation;
- compound assignment and pre/post increment result behavior;
- high-level calls;
- `for`/`continue` semantics;
- checked arithmetic and panics;
- return/revert/fallthrough completion;
- rollback after writes/logs before a later revert.

That is a lot, but it is at least one coherent proof problem.

### Rollback Needs A First-Class Semantics

The MiniVault walkthrough exposed this sharply. `AbstractYul` and `GeneratedYul`
both need a way to state that storage writes and logs in a frame are discarded on
revert. Without that, the compiler theorem will fail for realistic Solidity.

### GeneratedYul Must Stay Generated

The generated Yul profile should be defined before the compiler grows. If we
start accepting arbitrary Yul, the proof scope will balloon without helping the
Solidity-to-EVM theorem.

### StackCfg Needs Readable Planning

The public StackCfg can be positional, but the compiler pass likely needs an
internal symbolic stack planner. Otherwise every proof becomes unreadable
`DUP`/`SWAP` accounting too early.

## Recommended Next Step

Before refactoring all Lean folders, implement a tiny end-to-end design slice in
docs or Lean:

```text
valid Solidity local variable + checked arithmetic + return
  -> AbstractYul let/checked-add/return
  -> GeneratedYul memory return convention
  -> StackCfg
  -> Bytecode
  -> gasless EVM return behavior
```

Then add, in order:

1. modifier prelude-only expansion;
2. short-circuit or ternary;
3. storage read/write;
4. revert rollback;
5. event logs;
6. external call failure.

That sequence tests the new shorter spine without letting the hardest EVM
features swamp the first proof.
