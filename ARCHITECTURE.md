# Solid Core Architecture

This repository is an **executable Lean semantics of the Solidity 0.8.35 source
language**. Its external-world model is expressed in the *same interaction
monad* that `../evm-compiler` (Solidus) uses for its Yul source semantics and
EVM target semantics, on the same Lean toolchain and EVMYulLean pin, so a future
Solidity→Yul lowering can be stated as a refinement without re-plumbing the
boundary.

This branch is **only the Solidity source semantics**. There is no
Solidity→Yul lowering, no `ForwardRel` proofs, and no compiler artifacts
(the former `EvmYul` library, `Spine`/`L0x` layout, generated Yul, bytecode,
and EVM parity harnesses are all removed). The end state is a single
`lean_lib SolidCore`.

## What this repository claims

It is an **executable, differentially-validated** semantics of Solidity 0.8.35.
The verification is a differential corpus, **not theorems**:

- **99 paired Forge/pinned-solc cases** (`tests/forge-harness/`), covering real
  OpenZeppelin, WETH9, solmate, Uniswap, and Compound sources, plus targeted
  frontier cases.
- **426 Lean `#eval` assertions** checked against the pinned-solc/Foundry-EVM
  observable behavior of those cases.
- **~311 pinned-solc rejection lanes** (`solc_rejects`) paired against the
  common typechecker's acceptedness witnesses.

There are **no proofs on this branch** — no theorem relates this semantics to
compiled Yul or EVM bytecode. The corpus is the whole of the evidence. Any
statement stronger than "this executable model agrees with pinned solc 0.8.35
on the corpus" is out of scope until the lowering project begins. The intended
future direction is sketched in `docs/compile-to-yul-readiness.md`; it is a
*study*, not a claim.

## Substrate

Matched to `evm-compiler` exactly so the shared types are literally identical:

- **Lean toolchain**: `leanprover/lean4:v4.28.0`.
- **EVMYulLean**: `danrobinson/EVMYulLean @ 3c5c44a6` as a real Lake git
  dependency. `State`, `SharedState`, `Substate`, `UInt256`, account/log/block
  types come from the pin — no local shims. The former local
  `EvmYul.UInt256`/Keccak compatibility modules and the `external/nethermind`
  submodule are gone.
- **Keccak**: the pinned `EvmYul.SpongeHash.Keccak256` is FFI/opaque and
  unusable from a total interpreter, so this repo keeps a repo-owned *pure*
  Keccak (`SolidCore/Solidity/Keccak.lean`) with a corpus-gated byte-parity
  witness against the pinned FFI hash (`lake exe keccakParity`). This is the
  one deliberate local implementation of a pinned primitive, and it is checked,
  not silently shimmed.

## Module layout

Single library `SolidCore` (`lakefile.lean`, `@[default_target] lean_lib
SolidCore`), plus one executable `keccakParity` for the byte-parity witness.

```text
SolidCore/Solidity/
  Ast.lean          -- surface AST (imports only Shared; no ABI/Interpreter dep)
  Interface.lean    -- surface elaboration + solc-AST import surface
  TypeCheck.lean    -- the common (acceptedness) typechecker
  Checked.lean      -- checked executable projection + checked entry points
  Interpreter.lean  -- the one fuel-based interpreter; SolI monad + choke points
  ABI.lean          -- ABI encode/decode/dispatch
  Keccak.lean       -- repo-owned pure Keccak (byte-parity-checked vs the pin)
  Interaction.lean  -- bridge: re-exports the shared interaction alphabet
  Shared/           -- EVM-primitive foundations (Word, Account, Block, Call,
                       External, Log, Precompile), folded in from the former
                       SharedSemantics library
SolidCore/Witness/
  Interface.lean, TypeCheck.lean, Checked.lean, RationalConstants.lean
                    -- the entire example/witness corpus, out of the semantics
```

Splitting the interpreter's big mutual block across files is not possible in
Lean, so `Interpreter.lean` stays one file for the mutual core; "no monolith"
means no *mixed-concern* file (examples, typechecker, ABI, and the AST all live
in their own modules), not an arbitrary line limit.

## The external boundary: one interaction monad, not oracles

A Solidity execution *is* an interaction tree over the shared query alphabet.
`SolidCore/Solidity/Interaction.lean` re-exports, under stable names, the exact
`EvmCompiler.Simulation.*` declarations:

```text
Interaction  -- free monad: done (final state) | request (query) (answer → k)
Query/Answer -- resource (gas|msize) | external (OpenWorld, ExternalRequest)
OpenWorld    -- accounts (nonce, balance, storage, transient, code) + substate
ForwardRel   -- the composition relation Solidus's theorems are stated in
```

These come from the sibling **`../evm-interaction`** Lake path dependency — a
byte-identical verbatim extraction of `evm-compiler`'s Simulation sources. A
hash-check (`scripts/check_shared_interaction_hashes.py`, which reads
`../evm-compiler` read-only) guarantees the extracted files stay byte-for-byte
identical to evm-compiler's copies, so the alphabet cannot drift. This repo
programs against the real composition alphabet from day one; `evm-compiler`
adopts the package whenever its own freeze is next rev'd.

The interpreter's monad is
`SolI α := EvmCompiler.Simulation.Interaction SolidityFailure α`
(`Interpreter.lean` ~1804). The **only** request nodes are external calls
(call/staticcall/delegatecall/callcode, low- and high-level, precompile
staticcalls to addresses 1/2/3) and contract creations (`new`, create/create2).
Everything else — reverts, panics, control flow, fuel exhaustion — is a
Solidity-owned leaf value: reverts stay `Result.reverted` values and only
`.outOfFuel` (the distinguished truncation failure, mirroring Yul's
`.OutOfFuel`) escapes `Stmt.eval` as a throw. Environment reads Yul also takes
from shared state (block/tx fields, blockhash) are state reads, **not** queries,
matching the alphabet exactly.

### Scripted responders

The corpus does not execute a real second contract (closed-world multi-contract
execution is out of scope by design — reentrancy and `this.f()` are
environment-answered). Fixture answers are supplied by **scripted responders**:
a per-case ordered list of oracle rows, built by
`responderOfResults [callRows] [createRows]` and folded fail-closed by
`SolI.runWith`. A witness entry named `…UnderResponder N (responderOfResults …)`
answers each external query from the rows and **fails closed** on any
unanticipated request (`ResponderFailure.unmatched`, carrying the request for an
expected-vs-actual diff) rather than silently continuing on a failed call. This
makes "the fixture intends this call to fail" (an explicit `success := false`
row) and "the fixture never anticipated this request" distinguishable.

## Boundary rules (updated for the interaction model)

- **Storage layout is IN scope (spec-owned).** Unlike compiler memory layout,
  Solidity's storage layout (slots, packing, mapping/array slot derivation) is
  *documented language spec* that upgradeable-contract and cross-contract tools
  rely on. The repo models slots/packing/paths and can materialize a word-
  addressed storage snapshot for the `OpenWorld` a query carries.
- **Memory layout remains OUT of scope.** Memory stays abstract; it reaches
  queries only through ABI-encoded calldata bytes, which the ABI layer already
  concretizes.
- **The external world is the shared query alphabet, not oracles.** External
  calls/creates emit `Query.external`; non-self accounts are reads of an
  `OpenWorld`-shaped environment, not ad-hoc oracle-record lookups. The old
  oracle-record `Context` fields are deleted.

## Frozen corpus

The conformance corpus and the typechecker-acceptedness (`solc_rejects`) lanes
are **frozen regression suites**, not a growing coverage target. New lanes are
added **only to pin a discovered bug** — as the `rational-constants` lane does
(the A1 over-reject) and the planned recursion/function-boundary lane will — and
**never to extend coverage**. The open-ended acceptedness audit of the previous
roadmap is closed, not continued. See `tests/README.md` for the same rule.

## Known gaps

Deferred semantic gaps (intra-frame balance accounting, `gasleft` as a resource
query, create initCode being source-canonical rather than compiled bytecode,
internal-function recursion / deep call-nesting beyond the inline budget) are
recorded explicitly in `ROADMAP.md`'s "Known semantic gaps" registry and in
`docs/DECISIONS.md`, not silently absent. Each is fixed with paired Forge lanes
when it is picked up.
