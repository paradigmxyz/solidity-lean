# Coordination

Coordination uses append-only Markdown logs. Code and theorem statements remain
the source of truth.

The project lives at `/Users/dan/Public/solid-core-spine`.

The point of coordination is momentum toward a complete source-to-EVM theorem,
not strict territorial control. The ownership list says who should notice and
care most about each area. Agents may make small cross-boundary edits when that
keeps the spine moving, but should leave a short log note when the edit changes
another agent's expected surface.

## Ownership

- `supervisor` reads across the whole tree and critiques whether current work is
  moving toward a non-vacuous complete theorem.
- `source-model` owns `SolidCore/Spine/L00_Source` and source semantics exports.
- `target-model` owns `SolidCore/Spine/L08_Evm` and final target semantics exports.
- `pass-01-source-to-accepted` owns `L01_Accepted` and `P01_SourceToAccepted`.
- `pass-02-accepted-to-control` owns `L02_Control` and `P02_AcceptedToControl`.
- `pass-03-control-to-effect` owns `L03_Effect` and `P03_ControlToEffect`.
- `pass-04-effect-to-layout` owns `L04_Layout` and `P04_EffectToLayout`.
- `pass-05-layout-to-generated-yul` owns `L05_GeneratedYul` and
  `P05_LayoutToGeneratedYul`.
- `pass-06-generated-yul-to-stackcfg` owns `L06_StackCfg` and
  `P06_GeneratedYulToStackCfg`.
- `pass-07-stackcfg-to-bytecode` owns `L07_Bytecode` and
  `P07_StackCfgToBytecode`.
- `pass-08-bytecode-to-evm` owns `P08_BytecodeToEvm` and final adapter proof
  artifacts. It should treat `L07_Bytecode` and `L08_Evm` as read-mostly and
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
