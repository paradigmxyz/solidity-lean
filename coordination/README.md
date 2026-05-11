# Coordination

Coordination uses append-only Markdown logs. Code and theorem statements remain
the source of truth.

## Ownership

- `source-model` owns `SolidCore/Spine/L00_Source` and source semantics exports.
- `target-model` owns `SolidCore/Spine/L10_Evm` and final target semantics exports.
- `pass-01-source-to-accepted` owns `L01_Accepted` and `P01_SourceToAccepted`.
- `pass-02-accepted-to-control` owns `L02_Control` and `P02_AcceptedToControl`.
- `pass-03-control-to-effect` owns `L03_Effect` and `P03_ControlToEffect`.
- `pass-04-effect-to-layout` owns `L04_Layout` and `P04_EffectToLayout`.
- `pass-05-layout-to-structured-target` owns `L05_StructuredTarget` and
  `P05_LayoutToStructuredTarget`.
- `pass-06-structured-to-symbolic-target` owns `L06_SymbolicTarget` and
  `P06_StructuredToSymbolicTarget`.
- `pass-07-symbolic-to-concrete-target` owns `L07_ConcreteTarget` and
  `P07_SymbolicToConcreteTarget`.
- `pass-08-concrete-to-stackcfg` owns `L08_StackCfg` and
  `P08_ConcreteToStackCfg`.
- `pass-09-stackcfg-to-bytecode` owns `L09_Bytecode` and
  `P09_StackCfgToBytecode`.
- `pass-10-bytecode-to-evm` owns only `P10_BytecodeToEvm` and non-target adapter
  proof artifacts; it may not edit `L09_Bytecode` or `L10_Evm`.

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
