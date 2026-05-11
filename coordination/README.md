# Coordination

This folder contains the static coordination contract for agents working on the
spine. It is intentionally small; code, theorem statements, tests, and commits
are the durable project record.

Every agent should read `ARCHITECTURE.md`, this file, the folder README for the
area it touches, and the adjacent layer/pass interfaces before editing.

## Agents

- `layer-00-source-solidity`: source syntax and source semantics.
- `layer-01-valid-solidity`: validity, resolution, typechecking, and the
  `SourceSolidity -> ValidSolidity` checker.
- `layer-02-abstract-yul`: AbstractYul and the hard source-to-IR lowering pass.
- `layer-03-generated-yul`: generated Yul profile and concrete layout/ABI
  lowering.
- `layer-04-stackcfg`: stack CFG, stack planning, and CFG wellformedness.
- `layer-05-bytecode`: assembler, byte encoding, PC maps, and jump adequacy.
- `layer-06-evm`: public EVM semantics and Forge/parity evidence.
- `supervisor`: whole-project critique for skipped layers, vacuous claims,
  fixture-shaped routes, and untracked assumptions.

Agents may make small adjacent edits when that keeps the spine moving. Larger
cross-boundary changes should update the affected interfaces and mention the
reason in the commit message or handoff, not in a separate scratch log.

## Shared Rules

- Public claims compose through the spine in `ARCHITECTURE.md`.
- Do not add fixture/story compiler routes.
- Do not define a layer's semantics by compiling it to the next layer.
- Do not make wellformedness mean "the next pass succeeds."
- Treat tests, Forge, fuzzing, and corpus replay as evidence, not proof.
- Delete dead routes instead of preserving compatibility paths that invite
  agents to skip layers.
