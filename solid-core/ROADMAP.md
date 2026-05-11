# Roadmap

## Full Solidity To FullYul

The Lean Solidity interpreter is the formal source semantics. Parser output,
Solar output, solc JSON, and Forge fixtures are ingestion or test evidence until
Lean rechecks them as accepted source programs. The compiler theorem should
relate that checked source semantics to execution of the emitted sibling
`SolidCoreYulCore.FullYul` program.

Roadmap in one sentence:

```text
accepted Solidity source
  -> Lean Solidity interpreter
  -> checked/typed Core
  -> zero or more semantics-bearing IR passes
  -> accepted-profile FullYul AST
  -> sibling FullYul interpreter
  -> same observable behavior
```

The equivalence work splits into two claims:

1. Source-model claim: the Lean interpreter is the intended model of the
   accepted Solidity subset. This is supported by frontend rechecking,
   differential tests, and later any available formal Solidity reference, but it
   is not the compiler theorem by itself.
2. Compiler-preservation claim: accepted Lean Solidity execution and emitted
   accepted-profile FullYul execution have matching observable behavior.

The public compiler claim should remain split into success soundness and
coverage:

```text
compile_sound:
  if Lean accepts a checked Solidity AST and compilation returns FullYul,
  then the emitted accepted-profile FullYul refines the Solidity interpreter.

compile_complete_for_accepted:
  every program in the current accepted subset compiles successfully.
```

The composed milestone theorem is `compile_complete_for_accepted` followed by
`compile_sound`. This keeps semantic preservation separate from feature
coverage, which is important while the accepted subset grows.

Observables include normal returns, reverts, storage changes, logs/events,
function-call outcomes, ABI-shaped input/output data, and fuel/resource
conditions made explicit in the theorem assumptions.

## Phases

- [x] Use the sibling `SolidCoreYulCore.FullYul` AST and interpreter as the
  active target boundary, not a vendored local copy.
- [ ] Stabilize the Lean Solidity interpreter for the accepted subset. It must
  handle lexical scopes, locals, storage, switch, control flow,
  checked/unchecked arithmetic, arrays/bytes, events, custom reverts,
  ABI-shaped calls, and abstract function dispatch in arbitrary combinations.
- [ ] Add untrusted frontend ingestion for Solidity syntax. Solar, solc JSON, or
  another parser may build candidate syntax, but Lean must recheck names, types,
  scopes, storage locations, and accepted-feature boundaries before any theorem
  applies.
- [x] Define `AcceptedSource` separately from interpreter executability.
  Unsupported Solidity should be rejected by the accepted-source checker rather
  than silently falling outside the proof.
- [ ] Elaborate accepted Solidity into typed Core. Core removes parser and
  surface-language clutter while preserving lexical scopes, storage identity,
  control outcomes, reverts, logs, and function-call structure.
- [ ] Prove `source_to_core_correct`: source interpreter evaluation and Core
  evaluation produce matching outcomes, state, logs, return data, revert data,
  and explicit fuel/resource conditions.
- [ ] Split Core only where a pass earns its keep. Likely later IRs are:
  control/effect Core for abrupt outcomes, layout Core for locals/storage/ABI,
  and a Yul-shaped Core for names, blocks, loops, and function definitions.
- [ ] Give every verified IR executable or relational semantics plus a named
  preservation/refinement theorem. No IR participates in the public theorem just
  because it is convenient implementation structure.
- [ ] Lower the final IR to sibling FullYul while carrying static-checker,
  `CompilerEmittable`, and accepted-profile evidence for every emitted
  expression and statement.
- [ ] Prove `core_to_fullyul_correct`: FullYul execution simulates the final IR
  under explicit relations for locals, scopes, storage slots, ABI buffers,
  return slots, reverts, logs, control outcomes, functions, and fuel.
- [ ] Compose `compile_solidity_to_fullyul_correct`: if Lean accepts a Solidity
  program and compilation succeeds, executing emitted accepted-profile FullYul
  matches the Lean Solidity interpreter on the same observable behavior.

## Minimum Vertical Route

- [ ] Interpreter-complete MVP: choose the smallest accepted subset containing
  switch, storage, builtins, locals/scopes, conditionals, loops, returns, and
  reverts; ensure the Lean interpreter supports arbitrary nesting of these
  constructs.
- [ ] Accepted-source checker: accept exactly that MVP and expose a theorem that
  accepted programs have the well-formed names, scopes, storage slots, and type
  facts needed by elaboration.
- [ ] Source-to-Core pass: implement one recursive elaborator from accepted
  Solidity statements/expressions into typed Core, with lexical scopes,
  function frames, storage slots, control outcomes, reverts, and switch cases
  explicit in the Core syntax.
- [ ] Core semantics theorem: prove the recursive preservation theorem once for
  each construct, so nesting follows by induction rather than by separate
  conditional-inside-loop and loop-inside-conditional proofs.
- [ ] Optional Core-to-Core passes: introduce only IRs that simplify a named
  proof obligation, such as control normalization, storage/layout assignment,
  ABI shaping, or Yul block/function structuring.
- [ ] Core-to-FullYul pass: compile Core into FullYul using the current
  `CompilerProfile.currentSolidCore` where possible and explicit profile
  extensions only when the compiler emits a new Yul construct.
- [ ] FullYul profile theorem: prove every emitted statement satisfies the
  accepted profile before including it in the main compiler theorem.
- [ ] End-to-end theorem: compose source-to-Core and Core-to-FullYul preservation
  into the public compiler theorem for the MVP.
- [ ] Expand one semantic family at a time after the theorem exists: arrays,
  bytes, richer ABI, events, internal calls, custom errors, external calls, and
  then the broader Solidity surface.

## Coverage Milestones

- [x] Pure expression returns and basic FullYul expression emission.
- [x] Checked and unchecked arithmetic slices with revert behavior where needed.
- [x] Compositional statement slices for sequencing, blocks, unchecked wrappers,
  locals, conditionals, and simple loops.
- [x] Forge parity subjects represented as ordinary Solidity AST and executable
  through the Lean interpreter.
- [ ] General Solidity-to-Core elaboration for arbitrary combinations of the
  current interpreter features, rather than fixture-specific compiler cases.
- [ ] Switch lowering and proof through the same control/effect machinery used
  for conditionals and loops.
- [ ] Storage load/store lowering and proof through an explicit source/Yul
  storage relation.
- [ ] Basic builtin coverage for the MVP accepted subset, with each builtin tied
  to the FullYul compiler profile before it enters the main theorem.
- [ ] Function calls, returns, reverts, and frame/scoping behavior handled
  compositionally through Core/IR semantics.
- [ ] Differential harness that runs Solidity fixtures against the Lean
  interpreter and then against compiled FullYul as regression evidence outside
  the proof boundary.
- [ ] External calls admitted only through an explicit FullYul profile extension
  with abstract event semantics before they are included in the main theorem.

## Completion Rule

A Solidity feature is complete only when it has source semantics, accepted-source
checking, Core/IR elaboration, pass preservation, FullYul emission/profile
evidence, and coverage under the composed compiler theorem. Until then it is
either executable-only or experimental.
