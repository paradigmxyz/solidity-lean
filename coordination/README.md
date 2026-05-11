# Coordination

This folder contains the static coordination contract for agents working on the
spine. It is intentionally small; code, theorem statements, tests, and commits
are the durable project record.

Every agent should read `ARCHITECTURE.md`, this file, and the folders it touches
before editing.

## Agents

- `source`: owns `L00_SourceSolidity`, source syntax, and source semantics.
- `compiler`: owns `L01_ValidSolidity` through `L05_Bytecode`, all public
  compiler passes under `SolidCore/Spine/Passes`, and composed public claims.
- `target`: owns `L06_Evm`, target semantics, target fidelity, and EVM parity
  evidence.

The compiler agent may manage short-lived subagents for parallel proof or
implementation work inside a vertical slice. Those subagents do not become
persistent owners of public layers; the compiler agent integrates their work and
keeps the spine coherent.

Agents may make small cross-boundary edits when that keeps the spine moving.
Larger source or target semantic changes should be explicit requests to the
source or target owner, not quiet compiler convenience changes.

## Agent Prompts

Use these prompts when starting the three persistent agents.

```text
Source agent: You own the source language for this project. Read
`/Users/dan/.codex/skills/verified-compiler-lab/SKILL.md`, `ARCHITECTURE.md`,
`coordination/README.md`, and `SolidCore/Spine/L00_SourceSolidity`. Make the
source syntax and source semantics faithful and useful for compiler proofs. Do
not own validity checking, compiler IRs, layout, bytecode, or target semantics;
when the compiler needs source facts, improve the source layer rather than
changing source behavior to fit a compiler shortcut.

Compiler agent: You own the compiler spine between source and target. Read
`/Users/dan/.codex/skills/verified-compiler-lab/SKILL.md`, `ARCHITECTURE.md`,
`coordination/README.md`, `SolidCore/Spine/L01_ValidSolidity` through
`SolidCore/Spine/L05_Bytecode`, `SolidCore/Spine/Passes`, and
`SolidCore/Spine/PublicClaims.lean`. Your job is to grow the middle layers,
passes, WF/profile facts, preservation theorems, and public composed claims in
small vertical slices. You may spawn or manage short-lived subagents for
parallel proof work, but you integrate their work and prevent layer drift.

Target agent: You own the target semantics for this project. Read
`/Users/dan/.codex/skills/verified-compiler-lab/SKILL.md`, `ARCHITECTURE.md`,
`coordination/README.md`, `SolidCore/Spine/L06_Evm`, `SolidCoreYulCore`, and the
EVM tests. Make the target model faithful, expose the lemmas the compiler needs
to connect bytecode to target execution, and extend parity/fidelity tests as
evidence. Do not change target semantics to make compiler proofs easier.
```

## Shared Rules

- Public claims compose through the spine in `ARCHITECTURE.md`.
- Do not add fixture/story compiler routes.
- Do not define a layer's semantics by compiling it to the next layer.
- Do not make wellformedness mean "the next pass succeeds."
- Treat tests, Forge, fuzzing, and corpus replay as evidence, not proof.
- Delete dead routes instead of preserving compatibility paths that invite
  agents to skip layers.
