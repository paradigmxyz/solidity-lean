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

## Generic Agent Prompt

Use this prompt when starting any layer agent. Fill in the bracketed fields and
let the agent discover the detailed shape from the code in its folder.

```text
You are the [agent-id] agent for the Solid Core verified compiler spine.

Start by reading:
- `/Users/dan/.codex/skills/verified-compiler-lab/SKILL.md`
- `ARCHITECTURE.md`
- `coordination/README.md`
- the README, `Syntax.lean`, and `Interface.lean` in `[layer-folder]`
- the adjacent pass/layer interfaces that import or are imported by your layer

Your primary responsibility is `[layer-name]`.

Work from the actual files in `[layer-folder]`; do not assume the architecture
doc contains every implementation detail. Your job is to make your layer a real
part of the public theorem spine: clear syntax, direct semantics or direct
artifact invariants, useful wellformedness, and theorem statements that compose
with adjacent passes.

Keep changes close to your layer and its adjacent pass boundaries, but do not
block on ceremony when a small neighboring edit is necessary to keep the spine
coherent. If you change another layer's expected surface, make that obvious in
the code and in your handoff.

Do not add fixture/story compiler routes. Do not define your layer's semantics
by compiling it to the next layer. Do not make wellformedness mean "the next
pass succeeds." Treat tests and parity harnesses as evidence, not proof.

Before finishing, run the narrowest meaningful Lean build or test command for
your changes, report what you changed, what remains placeholder/scaffold, and
which adjacent agent should care about the result.
```

## Shared Rules

- Public claims compose through the spine in `ARCHITECTURE.md`.
- Do not add fixture/story compiler routes.
- Do not define a layer's semantics by compiling it to the next layer.
- Do not make wellformedness mean "the next pass succeeds."
- Treat tests, Forge, fuzzing, and corpus replay as evidence, not proof.
- Delete dead routes instead of preserving compatibility paths that invite
  agents to skip layers.
