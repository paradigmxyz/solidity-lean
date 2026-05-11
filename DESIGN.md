# Solid Core Top-Down Design

This document describes the intended compiler spine from the final theorem
backward. It is a design-pressure document: the Lean files remain the source of
truth, and this file should change when the spine changes.

## Final Theorem Shape

The project is aiming for a theorem that says: for every independently checked
source program, recursive compiler passes produce EVM bytecode whose execution
is behaviorally compatible with the source semantics.

In rough form:

```text
checked Solidity
  -> desugared Solidity core
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

## Public Spine

The current Lean spine is:

```text
L00_Source
  -> L01_CheckedSolidity
  -> L02_DesugaredSolidity
  -> L03_Control
  -> L04_Effect
  -> L05_Layout
  -> L06_GeneratedYul
  -> L07_StackCfg
  -> L08_Bytecode
  -> L09_Evm
```

This is a real public layer because it will handle Solidity features such as
modifiers, declaration sugar, or other source forms whose meaning is best
explained as a rewrite into a simpler Solidity core. Checking should answer
"is this input in scope, and what name/type/declaration facts have been
established?" Desugaring should answer "what simpler source program has the same
meaning?" Control lowering should then focus on sequencing,
branches, loops, exits, and continuations rather than rich Solidity surface
syntax.

## Layer And Pass Design

### L00_Source

Role: the Solidity-like source AST and source interpreter. This is the semantic
starting point for the theorem.

It should own source syntax, source runtime state, source evaluation, and the
meaning of language constructs before compiler-imposed restrictions. It should
not be reshaped to make later passes easier. If a source feature is awkward to
compile, the checked subset or compiler pass should narrow or reject it.

Current status: `L00_Source` re-exports the copied Solidity source AST and
interpreter.

### P01_SourceToCheckedSolidity

Role: independent Solidity checking.

The pass should decide whether a source AST is inside the verified subset and
return a checked artifact with proof-relevant evidence. Its soundness theorem
should say that successful checking implies the feature, name/scope, type, and
declaration facts carried by `L01_CheckedSolidity`. Its completeness theorem
should say that anything satisfying the checked predicate can be produced by the
checker.

Design pressure: this pass must not become "checked means the compiler
succeeds." It is the front gate for feature boundaries, name/scope/type facts,
and any source assumptions later passes rely on.

### L01_CheckedSolidity

Role: the verified and checked source artifact.

It should own checked-input facts: supported feature boundaries, name resolution,
scoping, typing, declaration shape, modifier validity, external-call assumptions,
and source wellformedness. It should not own a new semantics separate from source
unless the checked language has genuinely different UB/error rules. Usually its
semantics should be source semantics plus checked facts.

Current status: `L01_CheckedSolidity` now returns a checked `Program` artifact
and has explicit placeholder fact families for names/scopes, types, and
declarations. Those placeholders need to become real checks before later passes
depend on them.

### P02_CheckedSolidityToDesugaredSolidity

Role: rewrite checked Solidity into a smaller Solidity core.

The pass should recursively remove source-level sugar while preserving source
semantics. Modifiers are the motivating example: a function with modifiers
should become an ordinary body whose prelude, placeholder/body position, and
postlude behavior are represented explicitly in the desugared source core.

Other candidates include declaration sugar, simple syntactic conveniences, and
source forms whose meaning is cleaner as source-to-source rewrites than as
control-flow compiler rules. The theorem should say desugared-source evaluation
matches checked-source evaluation.

Design pressure: do not use this layer for layout, stack, or bytecode concerns.
It is still Solidity-level.

### L02_DesugaredSolidity

Role: a simpler Solidity core after source-to-source rewriting.

It should own the smaller source grammar that later passes compile: explicit
modifier expansion, normalized declaration forms, and any source constructs that
make control lowering uniform. It should not own continuation semantics,
explicit effects, storage/memory layout, generated Yul, or target behavior.

Current status: this layer is present in the Lean spine. It is identity-shaped
for now and carries placeholder facts that modifiers and unsupported surface
sugar have been removed.

### P03_DesugaredSolidityToControl

Role: elaborate desugared source into a control-normalized core language.

The pass should remove source surface irregularities while preserving source
behavior: nested blocks, switches, loop exits, return/revert propagation, and
statement sequencing should become a smaller recursive control language. The
main theorem should say control evaluation equals checked source evaluation for
all checked programs.

Current Lean status: `source_to_control_sound` composes `P01`, `P02`, and `P03`
through `L03_Control`.

### L03_Control

Role: source-level control flow made explicit and proof-friendly.

It should own structured control semantics: sequencing, branching, loop exits,
return/revert results, and continuation-like facts needed to prove recursive
compiler correctness. It should not own storage/memory layout decisions, stack
shape, byte encoding, or EVM gas-level concerns.

This layer is worth keeping if it becomes the place where arbitrary nested
source control is proved once and then reused. If it remains a thin mirror of
source syntax, it should be collapsed back into `L01_CheckedSolidity`.

With the proposed desugaring layer, this should not need to know about
modifiers. It should consume a simpler source core.

### P04_ControlToEffect

Role: make effects explicit without changing control behavior.

The pass should turn source-level expressions and statements into an IR where
reads, writes, calls, logs, returns, reverts, and exceptional exits are explicit
enough that later layout lowering does not need to rediscover them. The theorem
should say explicit-effect evaluation refines or equals control evaluation.

Current status: identity pass.

### L04_Effect

Role: explicit operational effects.

It should own effect sequencing, state transitions, expression evaluation order,
call/log/revert/return behavior, and the facts needed to separate "what happens"
from "where bytes live." It should not own ABI offsets, storage slot formulas,
memory word layout, stack-depth proof, or bytecode jump resolution.

This layer is probably right, but only if it becomes real. It is the natural
place to prevent `L05_Layout` from becoming a tangled mix of source semantics
and low-level addressing.

### P05_EffectToLayout

Role: choose and expose concrete data layout.

The pass should annotate or transform effectful programs with enough layout
facts for memory, calldata, ABI encoding/decoding, storage slots, logs, revert
payloads, and return data. The theorem should say layout-resolved evaluation
matches explicit-effect evaluation under the exported layout facts.

Current status: identity pass with placeholder `LayoutFacts`.

### L05_Layout

Role: low-level data layout before code generation.

It should own source-to-machine data placement facts: variable locations,
storage slot formulas, ABI head/tail offsets, memory allocation discipline,
calldata decoding, return/revert encoding, and event topic/data layout. It
should not own Yul syntax, stack CFG labels, byte offsets for jumps, or EVM
opcode semantics.

This layer should stay. Solidity-to-EVM proofs usually get stuck in layout
details; isolating them before generated Yul is likely to pay for itself.

### P06_LayoutToGeneratedYul

Role: lower layout-resolved source into the generated Yul subset.

The pass should recursively emit Yul-shaped statements that use only constructs
our compiler can generate and prove. Its artifact should include generated-subset
wellformedness and any fuel/profile evidence needed by the generated Yul
interpreter. The theorem should say generated Yul behavior refines the
layout-resolved semantics.

Design pressure: this is not a general Solidity-to-Yul or Yul-validation pass.
The source of truth is what the higher layers generate.

### L06_GeneratedYul

Role: the generated Yul-shaped subset.

It should own the syntax and semantics of Yul constructs that the compiler emits:
blocks, lets, assignments, if/switch/loops if emitted, builtin calls, memory and
storage primitives, and the small set of control behavior needed by the backend.
It should not try to accept or verify arbitrary Yul programs.

This layer is right if it remains an emitted subset. It becomes dangerous if it
drifts back into "all Yul," because that would add proof burden without helping
the source-to-EVM theorem.

### P07_GeneratedYulToStackCfg

Role: lower generated structured control into a stack-machine CFG.

The pass should compile generated Yul statements into labeled blocks,
explicit stack effects, explicit branch targets, and a depth environment. The
main theorem should say CFG execution refines generated Yul execution, assuming
the generated-subset `WF` and produced stack-depth facts.

This is where structured control turns into control-flow graph obligations.

### L07_StackCfg

Role: stack-oriented control-flow graph before byte encoding.

It should own labels, blocks, pseudo-instructions if useful, stack layout,
depth checking, branch structure, and local proof facts such as closed labels and
maximum stack bounds. It should not own byte offsets, immediate-byte encoding,
or final EVM environment semantics.

This layer should stay. It is the right proof boundary between structured code
generation and bytecode resolution.

### P08_StackCfgToBytecode

Role: resolve the CFG into concrete bytecode.

The pass should choose byte offsets, encode opcodes and immediates, resolve
jump destinations, remove pseudo-instructions, and preserve the stack-safety
facts needed by bytecode execution. The theorem should relate CFG steps or
traces to bytecode execution under the produced bytecode `WF`.

### L08_Bytecode

Role: resolved bytecode as an artifact distinct from EVM semantics.

It should own byte arrays/opcodes, jumpdest resolution facts, no-jump-into-
immediate facts, stack-safety facts inherited from CFG, and encoding adequacy.
It should not define an alternative EVM. It should be the executable artifact
that `L09_Evm` runs.

This layer should stay. Removing it would force byte-offset and encoding
reasoning into either CFG proofs or the target semantics, both of which would
make the final theorem harder to compose.

### P09_BytecodeToEvm

Role: connect resolved bytecode to the target EVM model.

This is less a compiler pass than a final adequacy boundary. It should not
change the bytecode or redefine the EVM. Its theorem should say that wellformed
resolved bytecode is interpreted by the public EVM semantics used in the final
claim.

If an adapter is used for proof convenience, the adapter must be connected back
to the public EVM step relation or whatever target relation becomes final.

### L09_Evm

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
Source -> CheckedSolidity -> DesugaredSolidity -> Control -> Effect -> Layout
```

`Source`, `CheckedSolidity`, `DesugaredSolidity`, and `Layout` clearly need to exist
once the source language includes modifiers or similar surface features. The
remaining question is whether `Control` and `Effect` both earn their keep. I
think they should stay for now, because Solidity combines complicated control
exits with stateful effects, and separating those proof burdens is likely better
than discovering too late that one giant source-to-layout pass has become
unprovable.

The criterion should be practical:

- strengthen `L02_DesugaredSolidity` when checked source grows past the small
  core currently represented by the Lean interfaces;
- keep `L03_Control` if it develops reusable recursive theorems for nested
  sequencing, branching, loops, breaks, continues, returns, and reverts;
- keep `L04_Effect` if it develops an effect semantics that lets layout proofs
  ignore source control quirks;
- collapse them later only if one remains an identity wrapper after real
  features pass through the spine.

## Missing Pieces

The spine probably needs a small shared refinement/observation vocabulary before
the final theorem becomes serious. That does not need to be a public compiler
layer. It can live as proof support used by pass theorems.

The source side will also need a richer checked-input story:

- name binding and scope facts;
- type facts;
- variable/frame facts;
- storage layout declarations;
- ABI and selector facts;
- assumptions about external calls and environment observations.

Those belong in `L01_CheckedSolidity` or as evidence carried out of `P01`, not as hidden
preconditions in later compiler passes.

## Main Risks

- `CheckedSource` stays feature-flag-only, so later theorems assume facts that
  were never checked.
- `L04_Effect` and `L05_Layout` remain identity aliases, encouraging agents to
  skip the hard middle proofs.
- `L06_GeneratedYul.WF` becomes a tautology instead of a real generated-subset
  invariant.
- `L07_StackCfg.WF` does not grow real label/depth/layout obligations before
  bytecode proofs begin.
- `P09_BytecodeToEvm` becomes an alternate target semantics instead of an
  adequacy theorem for the public EVM.
- Public roots accidentally import tests, examples, old compilers, or shortcut
  routes that bypass the spine.

## Recommended Near-Term Order

1. Strengthen `L01_CheckedSolidity` enough that source features carry real facts.
2. Strengthen `L02_DesugaredSolidity` before modeling modifiers or other rich
   Solidity surface forms in the checked subset.
3. Make control normalization independently valuable by proving recursive control
   lemmas beyond the first `source_to_control_sound` theorem.
4. Decide the first real effect-IR shape before adding more layout details.
5. Rebuild layout around a small number of layout facts needed by the first
   generated Yul slice.
6. Implement a tiny layout-to-generated-Yul slice recursively, then follow
   it through StackCfg, Bytecode, and EVM for one complete theorem path.
7. Let the EVM lane continue expanding parity coverage, but treat that as target
   model evidence until Lean theorem coverage reaches it.
