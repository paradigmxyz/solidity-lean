# Critique Of Target Language Docs

This critique is local and provisional. Oracle review for this target spine is
pending in conversation:

```text
20260511-190754-solid-core-abstractyul-spine-critique-6220c34f
```

## Overall Readiness

The target spine is ready for detailed design iteration, but not yet ready for
large implementation across all layers. It has a clearer semantic purpose than
the transitional Lean spine because `Control` and pre-Yul `Layout` are gone and
`AbstractYul` owns the real middle proof boundary.

The target spine:

```text
Source
  -> CheckedSolidity
  -> DesugaredSolidity
  -> AbstractYul
  -> GeneratedYul
  -> StackCfg
  -> Bytecode
  -> Evm
```

Each layer has a plausible reason to exist:

- `CheckedSolidity` is static evidence.
- `DesugaredSolidity` is source-to-source simplification.
- `AbstractYul` is Yul-shaped, typed abstract effects.
- `GeneratedYul` is concrete generated Yul.
- `StackCfg` is stack/control-flow proof.
- `Bytecode` is byte-offset/encoding proof.
- `Evm` is target execution.

## Older Oracle Guidance Applied

The older oracle responses add four constraints that are now reflected in these
docs:

- Public claims should be AST-level and semantics-level. String recognizers,
  fixture routes, certificates, and Forge parity can be useful evidence, but
  they must not be the main theorem spine.
- `CheckedSolidity` should eventually be a resolved, typed AST with explicit
  local handles, storage locations, declaration identities, and scope facts. A
  string-keyed local environment is only a temporary checker/parser aid.
- Backend safety cannot stop at stack depth. `StackCfg` needs full program WF:
  label closure, branch target closure, block terminal discipline, stack layout
  compatibility, generated-label freshness, max-stack bounds, and
  pseudo-instruction elimination.
- Assumptions for ABI, storage layout, hashing, logs, gas, external calls, fuel,
  and host behavior need names in theorem statements or profile predicates.
  They should not live as prose attached to a broad correctness theorem.

## Strong Points

- The `AbstractYul` / `GeneratedYul` distinction is real. It separates typed
  abstract effects from concrete Yul builtins and layout.
- Dispatch-to-`switch` now lands in the right place: concrete Yul generation,
  not Solidity desugaring.
- Layout is no longer a vague pre-Yul layer. It is attached to a specific pass:
  `AbstractYul -> GeneratedYul`.
- The lower layers remain crisp: stack CFG, bytecode, and EVM each own a
  different proof burden.

## Main Open Risks

### AbstractYul May Become Too Large

`AbstractYul` could accidentally absorb half the compiler: functions,
continuations, storage abstractions, ABI types, call semantics, and event
semantics. If it becomes too expressive, proving `AbstractYul -> GeneratedYul`
may be as hard as proving Solidity directly.

Mitigation: keep `AbstractYul` Yul-shaped and small. Add abstract effects only
when the next generated-Yul slice needs them.

### DesugaredSolidity Needs A Clear Stopping Point

Desugaring should not become a second compiler. It should remove Solidity
surface features, not introduce Yul-only constructs or machine concepts.

Mitigation: forbid Yul `switch`, memory offsets, storage slots, and stack-like
operations from `DesugaredSolidity`.

### Source Function Calls Need A Deliberate Plan

Function calls straddle multiple layers:

- checked function IDs and signatures in `CheckedSolidity`;
- modifier/inheritance normalization in `DesugaredSolidity`;
- explicit call/evaluation behavior in `AbstractYul`;
- selector dispatch and ABI encoding in `GeneratedYul`.

This is likely the first place the docs need more precision.

### Environment Duplication Still Looms

Every layer has some environment story. The docs should make the transition
explicit:

- source lexical scopes;
- checked resolved names/types;
- desugared simplified lexical scopes;
- AbstractYul generated locals and abstract effect environment;
- GeneratedYul concrete Yul locals plus EVM-like state;
- StackCfg stack slots and labels;
- Bytecode/EVM machine state.

If two adjacent layers end up with identical environments, one layer is suspect.

### GeneratedYul Could Drift Toward Full Yul

The docs say generated subset only, but implementation pressure may pull toward
modeling arbitrary Yul. That would waste proof effort.

Mitigation: define generated-subset `WF` early and reject ungenerated constructs.

## Layer-Specific Critique

### Source

Good as a broad semantic starting point. The risk is overfitting source syntax
to the current compiler. Keep it source-like.

### CheckedSolidity

This layer is essential. The current docs correctly make it evidence-bearing.
The risk is that "checked" remains placeholder `True` facts too long. The
resolved AST should not keep bare variable names as the semantic identity of
locals; unique handles and explicit storage identities are the next real
boundary.

### DesugaredSolidity

Useful if it handles modifiers and source sugar only. It should not handle
dispatch-to-switch, ABI layout, or storage lowering.

### AbstractYul

This is the most important and least proven design choice. It should be the
first detailed doc to refine. We need a minimal syntax and a small list of
abstract effects for the first verified slice.

### GeneratedYul

The distinction from AbstractYul is good, but the docs need to be careful about
whether helper functions/procedures are allowed. If yes, their scoping and call
semantics need early treatment.

### StackCfg

Strong layer. It should survive architecture changes. The doc now needs to be
read as demanding `Program.WF`, not just `DepthChecked`.

### Bytecode

Strong layer. It should survive architecture changes.

### Evm

Strong target layer. It must stay independent of compiler convenience.

## Recommended Next Step

Before implementation, write one concrete tiny slice across the target spine:

```text
checked local variable + arithmetic + return
  -> desugared core
  -> AbstractYul lets/effects
  -> GeneratedYul mstore/return or pure return convention
  -> StackCfg
  -> Bytecode
  -> Evm
```

That slice will tell us whether `AbstractYul` is the right size. If it feels
like a thin wrapper, collapse it. If it absorbs concrete layout too early, split
or constrain it.
