# Certification blueprint

The plan of [CERTIFICATION_TARGET.md](../CERTIFICATION_TARGET.md) as a dependency graph that agents and CI
both read. [obligations.toml](obligations.toml) holds one node per obligation (an external function of
UniswapV2ERC20, UniswapV2Pair, UniswapV2Factory or Counter times an edge E2..E8), the shared premises,
specs and statements they rest on, the lemmas already proved toward them, and one goal per contract.
[scripts/blueprint/check.py](../../scripts/blueprint/check.py) audits it in Lean and writes
[status.json](status.json) and [status.md](status.md).

## A node

| Field | Meaning |
|---|---|
| `id` | `<contract>.<function>.<edge>` for an obligation; shared nodes are `premise.*`, `lemma.*`, `trust.*` |
| `kind` | `obligation`, `lemma`, `premise`, `spec`, `statement`, `trusted` (E0, E1), `external` (the solar driver), `deliverable` (work outside Lean, such as an exporter or a driver), `goal` |
| `statement` | one line: what the node claims |
| `decl`, `module` | the Lean declaration that discharges (or, for a premise, spec or statement, states) the node, and the module to import for it; absent while nobody has written it |
| `deps` | ids the node needs |
| `lane` | the owner lane: `e2-semantics` .. `e8-gas`, `premises`, `specs`, `integrator`, `loopvc-A` .. `loopvc-D` |
| `owner` | the lane's Pyramid thread id, or `unassigned` |
| `branch` | `owner/repo:branch` the work lands on; empty until assigned |
| `acceptance` | the exact check that delivers the node (for a Lean node, check.py reporting it proved) |
| `receipt` | only for deliverables, goals and external nodes, once delivered: `{sha = ..., check = <CI run URL or local log>}`; a Lean node's receipt is written by the checker into status.json, never by hand |
| `human_review` | true only for what a person must read and agree with (statements, premises, specs, trust boundaries), never for a proof |
| `note` | the decl's scope where it is narrower than the node (such as "at the caller 0x2000") |

## Status

The checker imports each node's module (a batch at a time, one module at a time when a batch does not
elaborate), and for each decl reads whether it is a proof or a statement and its transitive axioms
(`Lean.collectAxioms`, what `#print axioms` prints):

- `proved`: a proof whose axioms are only propext, Classical.choice and Quot.sound.
- `sorry`: a proof depending on sorryAx. `axioms`: a proof depending on any other axiom (native_decide's included).
- `statement-only`: the decl is a Prop or a predicate, not a proof.
- `missing`: no decl yet, or the decl is not in its module; for a deliverable or goal, no receipt yet.
- `unbuilt`: the decl's module is not built (or is out of date, by `lake build --no-build`) in this run. Nothing is known of it, and it is never ready: a build step for its module comes first.
- `delivered`: a deliverable, goal or external node with a receipt. Never `proved`: only the kernel checker proves.
- `trusted`, `external`: never proved by this checker.

A proved node's receipt in status.json is the commit and the CI run (or local log) of the checker run that proved it. A dep is satisfied when it is proved or delivered, a trusted or external boundary, or when it is a premise, spec or statement whose decl exists
(statement-only). A node is **ready** when it is not satisfied and all its deps are; ready nodes are
ordered by how many unsatisfied nodes depend on them, directly or not.

`proved` says the kernel accepted the declaration with clean axioms, not that the declaration states the
node: where its scope is narrower the node says so in `note` (UniswapV2ERC20's E3 is proved at the
caller 0x2000 only, so E3 itself, from any caller, stays open), and the reviewed statements are the
check on that. A hand-written functional model is a lemma, never an edge.

## Running it

Build the modules first (the refinement workflow's builds), then:

```
python3 scripts/blueprint/check.py --no-lean                                # graph only
python3 scripts/blueprint/check.py --baseline docs/blueprint/status.json    # audit, fail on a regression
python3 scripts/blueprint/check.py --write                                  # rewrite status.json and status.md
```

CI: the `blueprint` workflow checks the graph on every change to it. The refinement workflow runs the
audit after its builds and fails if a node that is `proved` in the committed status.json is not proved
now (or left the graph); it uploads the fresh status as the `blueprint-status` artifact and lists the
nodes it newly proves, which are committed to the baseline by copying that status.json (and status.md)
here. The baseline only ratchets up: a node leaves `proved` only by a reviewed change to status.json.

Modules generated from the GPL-3.0 port (Core, Pair, Factory, uv2_erc20, Slice/Gen and the rest) are not
committed; they exist only after the generation steps of the refinement workflow. A node whose module the
workflow does not build (ContractsUniswapV2TransferSlice, ContractsUniswapV2ERC20Certified,
ContractsUniswapV2ERC20NoCall and ContractsUniswapV2PairSpec at the time of writing) is `missing` until a
build step for it is added.
