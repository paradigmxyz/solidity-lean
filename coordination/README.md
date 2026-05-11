# Coordination

Coordination uses append-only Markdown logs. Code and theorem statements remain
the source of truth.

The project lives at `/Users/dan/Projects/solid-core-spine`.

The point of coordination is momentum toward a complete source-to-EVM theorem,
not strict territorial control. The ownership list says who should notice and
care most about each area. Agents may make small cross-boundary edits when that
keeps the spine moving, but should leave a short log note when the edit changes
another agent's expected surface.

## Ownership

- `supervisor` reads across the whole tree and critiques whether current work is
  moving toward a non-vacuous complete theorem.
- `source-model` owns `SolidCore/Spine/L00_Source` and source semantics exports.
- `target-model` owns `SolidCore/Spine/L07_Evm` and final target semantics exports.
- `pass-01-source-to-checked-solidity` owns `L01_CheckedSolidity` and
  `P01_SourceToCheckedSolidity`.
- `pass-02-checked-solidity-to-desugared-solidity` owns
  `L02_DesugaredSolidity` and `P02_CheckedSolidityToDesugaredSolidity`.
- `pass-03-desugared-solidity-to-abstract-yul` owns `L03_AbstractYul` and
  `P03_DesugaredSolidityToAbstractYul`.
- `pass-04-abstract-yul-to-generated-yul` owns `L04_GeneratedYul` and
  `P04_AbstractYulToGeneratedYul`.
- `pass-05-generated-yul-to-stackcfg` owns `L05_StackCfg` and
  `P05_GeneratedYulToStackCfg`.
- `pass-06-stackcfg-to-bytecode` owns `L06_Bytecode` and
  `P06_StackCfgToBytecode`.
- `pass-07-bytecode-to-evm` owns `P07_BytecodeToEvm` and final adapter proof
  artifacts. It should treat `L06_Bytecode` and `L07_Evm` as read-mostly and
  coordinate any changes with the relevant logs.

## Working Norms

- Prefer touching your own layer/pass first, but do not block on ceremony for a
  small adjacent edit that obviously improves the spine.
- If a cross-boundary edit changes semantics, wellformedness, exported names, or
  theorem statements, note it in both relevant logs or in `supervisor.md`.
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
