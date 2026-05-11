# Solid Core Spine Roadmap

This repo now has one public verified-compiler spine. The copied pre-refactor
state is preserved in git; active development should not rebuild the old
example-specific compiler routes.

## Public Spine

```text
L00_Source
  -> L01_CheckedSolidity
  -> L02_DesugaredSolidity
  -> L03_Control
  -> L04_Effect
  -> L05_Layout
  -> L06_GeneratedYul
  -> L07_StackCfg
  -> L08_Bytecode
  -> L09_Evm
```

`L06_GeneratedYul` is the Yul-shaped subset produced by the higher compiler
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
      `SolidCore.Spine.PublicClaims.source_to_control_sound`.
- [x] Replace the thin accepted-input layer with `L01_CheckedSolidity`.
- [ ] Strengthen `L01_CheckedSolidity` from placeholder facts to real
      name/scope/type/declaration checking.
- [x] Insert `L02_DesugaredSolidity` before control lowering.
- [ ] Strengthen `L02_DesugaredSolidity` to remove modifiers and comparable
      Solidity surface sugar.
- [ ] Replace projection-based `L03_Control` semantics with independent
      recursive control semantics plus a source-to-control preservation theorem.
- [ ] Implement each later pass as recursive AST/artifact transformation rather
      than fixed-case recognizer.
- [ ] Add real `L07_StackCfg.WF` obligations before any bytecode/EVM claim.
- [ ] Add bytecode resolution correctness before any final target theorem.

## Deletion Policy

Delete obsolete example-specific routes instead of preserving compatibility wrappers.
If removal exposes a missing theorem, either prove the recursive pass theorem or
narrow the checked subset.

## Completion Rule

A feature is verified only when it is checked independently, transformed by
recursive compiler passes through the spine, and covered by a named Lean theorem
that reaches the declared target interpreter.
