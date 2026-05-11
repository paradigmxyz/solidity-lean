# Coordination

Coordination uses lightweight append-only Markdown logs. Code and theorem
statements remain the source of truth.

The project lives at `/Users/dan/Projects/solid-core-spine`.

The point of coordination is momentum toward a complete source-to-EVM theorem,
not strict territorial control. Each layer has one primary agent who should
notice and care most about that layer. Agents may make small adjacent edits when
that keeps the spine moving, but should leave a short log note when the edit
changes another agent's expected surface.

## Target Ownership

The target architecture is:

```text
L00_SourceSolidity
  -> L01_ValidSolidity
  -> L02_AbstractYul
  -> L03_GeneratedYul
  -> L04_StackCfg
  -> L05_Bytecode
  -> L06_Evm
```

Layer agents:

- `layer-00-source-solidity` owns source syntax and source semantics.
- `layer-01-valid-solidity` owns the validity artifact and the
  `SourceSolidity -> ValidSolidity` checker.
- `layer-02-abstract-yul` owns the AbstractYul language and the
  `ValidSolidity -> AbstractYul` lowering pass.
- `layer-03-generated-yul` owns the GeneratedYul subset and the
  `AbstractYul -> GeneratedYul` lowering pass.
- `layer-04-stackcfg` owns StackCfg and the `GeneratedYul -> StackCfg` pass.
- `layer-05-bytecode` owns Bytecode and the `StackCfg -> Bytecode` assembler.
- `layer-06-evm` owns the EVM target semantics and the `Bytecode -> Evm`
  embedding/adequacy theorem.
- `supervisor` reads across the whole tree and critiques whether current work is
  moving toward a non-vacuous complete theorem.

Agent prompts live in [LAYER_AGENT_PROMPTS.md](./LAYER_AGENT_PROMPTS.md).

## Working Norms

- Prefer touching your own layer and incoming pass first, but do not block on
  ceremony for a small adjacent edit that obviously improves the spine.
- If a cross-boundary edit changes syntax, semantics, wellformedness, exported
  names, compiler output, or theorem statements, note it in both relevant logs
  or in `supervisor.md`.
- Layer semantics and `WF` should describe the artifact itself, not merely say
  that some previous compiler produced it.
- Tests and parity runs are useful evidence, but public verification claims
  should eventually name Lean theorems that compose through the spine.
- Delete dead routes rather than preserving compatibility paths that invite
  agents to skip layers.

## Log Protocol

Each agent appends only to its own log. Requests to another agent are written as
`request(agent-id)` in the requester's log. Responses are written by the
requested agent in its own log as `response(agent-id)`.

Recommended tags:

```text
status
proof
api-change
request(agent-id)
response(agent-id)
blocked
decision
deletion
risk
handoff
```

Before starting, each agent reads this file, its own log, adjacent agents' logs,
the supervisor log, and any logs involved in pending requests.
