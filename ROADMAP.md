# Solid Core Spine Roadmap

This repo now has one public verified-compiler spine. The copied pre-refactor
state is preserved in git; active development should not rebuild the old
example-specific compiler routes.

## Public Spine

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

`L04_GeneratedYul` is the Yul-shaped subset produced by the higher compiler
layers. It is not a commitment to accept, model, or verify every possible Yul
program.

Public claims live under `SolidCore.Spine.PublicClaims`. Root imports should cite
the spine, not legacy compilers, generated source recognizers, parity harnesses,
or example certificates.

## Layer Contract

- [ ] Each layer has syntax or artifact type exports.
- [ ] Each layer has semantics or a relation to an adjacent semantic layer.
- [ ] Each layer exposes wellformedness/profile/resource assumptions needed by
      downstream passes.
- [ ] Each layer has a narrow interface module.

## Pass Contract

- [ ] Each pass reads only its source-layer interface and destination-layer
      interface.
- [ ] Each pass owns its compiler/checker function.
- [ ] Each pass proves success soundness.
- [ ] Each pass proves completeness for independently checked inputs when that
      is the right boundary.
- [ ] Each pass records assumptions as theorem hypotheses or artifact fields,
      not prose.

## Immediate Milestones

- [x] Copy both original worktrees into one public repo without nested git repos.
- [x] Preserve the copied baseline in an initial commit.
- [x] Delete public imports for legacy example-specific compiler paths.
- [x] Create the public layer/pass spine.
- [x] Add a lightweight supervisor loop to critique progress toward the complete
      theorem without turning coordination into a rigid permission system.
- [x] Keep the first public theorem AST-level and recursive:
      `SolidCore.Spine.PublicClaims.source_to_abstractYul_sound`.
- [x] Replace the thin accepted-input layer with `L01_CheckedSolidity`.
- [ ] Strengthen `L01_CheckedSolidity` from placeholder facts to real
      name/scope/type/declaration checking.
- [x] Insert `L02_DesugaredSolidity` before control lowering.
- [ ] Strengthen `L02_DesugaredSolidity` to remove modifiers and comparable
      Solidity surface sugar.
- [x] Collapse the placeholder `Control`, `Effect`, and pre-Yul `Layout` folders
      into the target `L03_AbstractYul -> L04_GeneratedYul` boundary.
- [ ] Replace transitional `L03_AbstractYul` semantics with a real Yul-shaped
      abstract-effect language plus a source-to-AbstractYul preservation theorem.
- [ ] Implement `L04_GeneratedYul` as a concrete generated Yul subset with named
      layout/profile assumptions.
- [ ] Implement each later pass as recursive AST/artifact transformation rather
      than fixed-case recognizer.
- [ ] Add real `L05_StackCfg.WF` obligations before any bytecode/EVM claim.
- [ ] Add bytecode resolution correctness before any final target theorem.

## Deletion Policy

Delete obsolete example-specific routes instead of preserving compatibility wrappers.
If removal exposes a missing theorem, either prove the recursive pass theorem or
narrow the checked subset.

## Completion Rule

A feature is verified only when it is checked independently, transformed by
recursive compiler passes through the spine, and covered by a named Lean theorem
that reaches the declared target interpreter.
