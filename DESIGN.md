# Solid Core Top-Down Design

This document describes the intended compiler spine from the final theorem
backward. It is a design-pressure document: the Lean files remain the source of
truth, and this file should change when the spine changes.

## Final Theorem Shape

The project is aiming for a theorem that says: for every independently accepted
source program, recursive compiler passes produce EVM bytecode whose execution
is behaviorally compatible with the source semantics.

In rough form:

```text
accepted source
  -> control-normalized source
  -> explicit-effect source
  -> layout-resolved source
  -> generated Yul subset
  -> stack CFG
  -> resolved bytecode
  -> EVM execution
```

Tests, Forge parity, fuzzing, and external traces are evidence. The verification
claim should eventually be a named Lean theorem that composes the adjacent pass
theorems through `SolidCore.Spine.PublicClaims`.

## Layer And Pass Design

### L00_Source

Role: the Solidity-like source AST and source interpreter. This is the semantic
starting point for the theorem.

It should own source syntax, source runtime state, source evaluation, and the
meaning of language constructs before compiler-imposed restrictions. It should
not be reshaped to make later passes easier. If a source feature is awkward to
compile, the accepted subset or compiler pass should narrow or reject it.

Current status: `L00_Source` re-exports the copied Solidity source AST and
interpreter.

### P01_SourceToAccepted

Role: independent acceptance checking.

The pass should decide whether a source AST is inside the verified subset and
return the same AST plus proof-relevant evidence. Its soundness theorem should
say that successful checking implies the accepted predicate. Its completeness
theorem should say that anything satisfying the accepted predicate is accepted by
the checker.

Design pressure: this pass must not become "accepted means the compiler
succeeds." It is the front gate for feature boundaries, name/scope/type facts,
and any source assumptions later passes rely on.

### L01_Accepted

Role: the verified source subset.

It should own accepted-input facts: supported feature boundaries, scoping,
typing, declaration shape, external-call assumptions, and source wellformedness.
It should not own a new semantics separate from source unless the accepted
language has genuinely different UB/error rules. Usually its semantics should be
source semantics plus accepted facts.

Current status: `L01_Accepted` is feature-flag based. That is a useful sketch,
but too weak for real Solidity compilation because it does not yet carry name,
scope, type, ABI, or storage-layout facts.

### P02_AcceptedToControl

Role: elaborate accepted source into a control-normalized core language.

The pass should remove source surface irregularities while preserving source
behavior: nested blocks, switches, loop exits, return/revert propagation, and
statement sequencing should become a smaller recursive control language. The
main theorem should say control evaluation equals accepted source evaluation for
all accepted programs.

Current status: this is the first real theorem-bearing pass:
`source_to_control_sound` composes `P01` and `P02` through `L02_Control`.

### L02_Control

Role: source-level control flow made explicit and proof-friendly.

It should own structured control semantics: sequencing, branching, loop exits,
return/revert results, and continuation-like facts needed to prove recursive
compiler correctness. It should not own storage/memory layout decisions, stack
shape, byte encoding, or EVM gas-level concerns.

This layer is worth keeping if it becomes the place where arbitrary nested
source control is proved once and then reused. If it remains a thin mirror of
source syntax, it should be collapsed back into `L01_Accepted`.

### P03_ControlToEffect

Role: make effects explicit without changing control behavior.

The pass should turn source-level expressions and statements into an IR where
reads, writes, calls, logs, returns, reverts, and exceptional exits are explicit
enough that later layout lowering does not need to rediscover them. The theorem
should say explicit-effect evaluation refines or equals control evaluation.

Current status: identity pass.

### L03_Effect

Role: explicit operational effects.

It should own effect sequencing, state transitions, expression evaluation order,
call/log/revert/return behavior, and the facts needed to separate "what happens"
from "where bytes live." It should not own ABI offsets, storage slot formulas,
memory word layout, stack-depth proof, or bytecode jump resolution.

This layer is probably right, but only if it becomes real. It is the natural
place to prevent `L04_Layout` from becoming a tangled mix of source semantics
and low-level addressing.

### P04_EffectToLayout

Role: choose and expose concrete data layout.

The pass should annotate or transform effectful programs with enough layout
facts for memory, calldata, ABI encoding/decoding, storage slots, logs, revert
payloads, and return data. The theorem should say layout-resolved evaluation
matches explicit-effect evaluation under the exported layout facts.

Current status: identity pass with placeholder `LayoutFacts`.

### L04_Layout

Role: low-level data layout before code generation.

It should own source-to-machine data placement facts: variable locations,
storage slot formulas, ABI head/tail offsets, memory allocation discipline,
calldata decoding, return/revert encoding, and event topic/data layout. It
should not own Yul syntax, stack CFG labels, byte offsets for jumps, or EVM
opcode semantics.

This layer should stay. Solidity-to-EVM proofs usually get stuck in layout
details; isolating them before generated Yul is likely to pay for itself.

### P05_LayoutToGeneratedYul

Role: lower layout-resolved source into the generated Yul subset.

The pass should recursively emit Yul-shaped statements that use only constructs
our compiler can generate and prove. Its artifact should include generated-subset
wellformedness and any fuel/profile evidence needed by the generated Yul
interpreter. The theorem should say generated Yul behavior refines the
layout-resolved semantics.

Design pressure: this is not a general Solidity-to-Yul or Yul-validation pass.
The source of truth is what the higher layers generate.

### L05_GeneratedYul

Role: the generated Yul-shaped subset.

It should own the syntax and semantics of Yul constructs that the compiler emits:
blocks, lets, assignments, if/switch/loops if emitted, builtin calls, memory and
storage primitives, and the small set of control behavior needed by the backend.
It should not try to accept or verify arbitrary Yul programs.

This layer is right if it remains an emitted subset. It becomes dangerous if it
drifts back into "all Yul," because that would add proof burden without helping
the source-to-EVM theorem.

### P06_GeneratedYulToStackCfg

Role: lower generated structured control into a stack-machine CFG.

The pass should compile generated Yul statements into labeled blocks,
explicit stack effects, explicit branch targets, and a depth environment. The
main theorem should say CFG execution refines generated Yul execution, assuming
the generated-subset `WF` and produced stack-depth facts.

This is where structured control turns into control-flow graph obligations.

### L06_StackCfg

Role: stack-oriented control-flow graph before byte encoding.

It should own labels, blocks, pseudo-instructions if useful, stack layout,
depth checking, branch structure, and local proof facts such as closed labels and
maximum stack bounds. It should not own byte offsets, immediate-byte encoding,
or final EVM environment semantics.

This layer should stay. It is the right proof boundary between structured code
generation and bytecode resolution.

### P07_StackCfgToBytecode

Role: resolve the CFG into concrete bytecode.

The pass should choose byte offsets, encode opcodes and immediates, resolve
jump destinations, remove pseudo-instructions, and preserve the stack-safety
facts needed by bytecode execution. The theorem should relate CFG steps or
traces to bytecode execution under the produced bytecode `WF`.

### L07_Bytecode

Role: resolved bytecode as an artifact distinct from EVM semantics.

It should own byte arrays/opcodes, jumpdest resolution facts, no-jump-into-
immediate facts, stack-safety facts inherited from CFG, and encoding adequacy.
It should not define an alternative EVM. It should be the executable artifact
that `L08_Evm` runs.

This layer should stay. Removing it would force byte-offset and encoding
reasoning into either CFG proofs or the target semantics, both of which would
make the final theorem harder to compose.

### P08_BytecodeToEvm

Role: connect resolved bytecode to the target EVM model.

This is less a compiler pass than a final adequacy boundary. It should not
change the bytecode or redefine the EVM. Its theorem should say that wellformed
resolved bytecode is interpreted by the public EVM semantics used in the final
claim.

If an adapter is used for proof convenience, the adapter must be connected back
to `L08_Evm.step` or whatever public target relation becomes final.

### L08_Evm

Role: the target machine semantics.

It should own the EVM state, instruction semantics, environment behavior, gas
where modeled, calls, creation, precompiles, logs, revert/return behavior, and
the observable result relation used in the final theorem.

It should not be compiler-shaped. The EVM agent can extend it toward completeness
using Forge parity and spec-driven tests, but the final theorem should mention
this target model directly.

Current status: it re-exports the copied bytecode/EVM model. The tests under
`tests/evm/forge-parity` are the right evidence lane for pushing this toward
complete EVM behavior.

## Are These The Right Layers?

My current answer: mostly yes, with one watchpoint in the middle.

The lower half looks right:

```text
GeneratedYul -> StackCfg -> Bytecode -> Evm
```

Those boundaries each buy a different kind of proof:

- generated structured semantics;
- stack-depth and control-flow graph invariants;
- byte-offset and encoding correctness;
- target-machine adequacy.

I would keep all four.

The upper half is also directionally right:

```text
Source -> Accepted -> Control -> Effect -> Layout
```

`Source`, `Accepted`, and `Layout` clearly need to exist. The only question is
whether `Control` and `Effect` both earn their keep. I think they should stay
for now, because Solidity combines complicated control exits with stateful
effects, and separating those proof burdens is likely better than discovering
too late that one giant source-to-layout pass has become unprovable.

The criterion should be practical:

- keep `L02_Control` if it develops reusable recursive theorems for nested
  sequencing, branching, loops, breaks, continues, returns, and reverts;
- keep `L03_Effect` if it develops an effect semantics that lets layout proofs
  ignore source control quirks;
- collapse them later only if one remains an identity wrapper after real
  features pass through the spine.

## Missing Pieces

The spine probably needs a small shared refinement/observation vocabulary before
the final theorem becomes serious. That does not need to be a public compiler
layer. It can live as proof support used by pass theorems.

The source side will also need a richer accepted-input story:

- name binding and scope facts;
- type facts;
- variable/frame facts;
- storage layout declarations;
- ABI and selector facts;
- assumptions about external calls and environment observations.

Those belong in `L01_Accepted` or as evidence carried out of `P01`, not as hidden
preconditions in later compiler passes.

## Main Risks

- `AcceptedSource` stays feature-flag-only, so later theorems assume facts that
  were never checked.
- `L03_Effect` and `L04_Layout` remain identity aliases, encouraging agents to
  skip the hard middle proofs.
- `L05_GeneratedYul.WF` becomes a tautology instead of a real generated-subset
  invariant.
- `L06_StackCfg.WF` does not grow real label/depth/layout obligations before
  bytecode proofs begin.
- `P08_BytecodeToEvm` becomes an alternate target semantics instead of an
  adequacy theorem for the public EVM.
- Public roots accidentally import tests, examples, old compilers, or shortcut
  routes that bypass the spine.

## Recommended Near-Term Order

1. Strengthen `L01_Accepted` enough that source features carry real facts.
2. Make `L02_Control` independently valuable by proving recursive control
   lemmas beyond the first `source_to_control_sound` theorem.
3. Decide the first real `L03_Effect` shape before adding more layout details.
4. Rebuild `L04_Layout` around a small number of layout facts needed by the first
   generated Yul slice.
5. Implement a tiny `P05` slice that emits generated Yul recursively, then follow
   it through StackCfg, Bytecode, and EVM for one complete theorem path.
6. Let the EVM lane continue expanding parity coverage, but treat that as target
   model evidence until Lean theorem coverage reaches it.
