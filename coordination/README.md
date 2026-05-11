# Coordination

Coordination uses append-only Markdown logs. Code and theorem statements remain
the source of truth.

## Ownership

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
- `pass-08-bytecode-to-evm` owns only `P08_BytecodeToEvm` and non-target adapter
  proof artifacts; it may not edit `L07_Bytecode` or `L08_Evm`.

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
and any logs involved in pending requests.
