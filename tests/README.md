# Tests

This directory holds executable evidence and regression suites for the Solidity
source semantics. Tests support the Lean semantics, but they do not replace the
source-language definitions under `SolidCore.Spine.L00_SourceSolidity`.

## Layout

- `cases/`: shared semantic cases for source-interpreter replay.
- `forge-harness/`: paired Forge/solc suites and Lean source-interpreter
  witnesses, run by `scripts/compare_forge_solc_interpreter.sh`. Cases may
  also declare a `solc_import` source contract; the harness asks solc for the
  Solidity AST and renders classified source nodes into the Lean source AST
  before running interpreter checks. For every Forge-bearing case, the harness
  first runs `forge test --list` without quiet output and fails closed if no
  tests are discovered, then runs the pinned-solc Forge test command. A case
  may declare `solc_rejects` source
  files whose pinned-solc rejection diagnostics are checked alongside the
  corresponding common-Lean-typechecker rejection witnesses. The shared
  manifest may assign a larger per-case `timeout` to heavyweight imported Lean
  witnesses without weakening the default bound for every other case. The
  shared
  corpus includes whole source-unit declaration coverage in
  `source-declarations`, AST frontier
  coverage for docs, interfaces, anonymous events, overrides, modifier
  overrides, `using {f}` function-list/global entries, private functions,
  function types, immutable/transient declarations, storage local references,
  operator spellings, constant-expression static array lengths, unit
  denominations, user-defined-value-type operator using in calls and
  constructors, constructor-time `using` method calls, and literal forms in
  `frontend-frontier`, broad
  expression-primitive coverage in
  `expression-primitives`, receive/fallback plus calldata byte/string/array
  slice, slice-index, and slice-local/do-while coverage in
  `entrypoint-slice-control`, and try/catch
  external-call routing in
  `try-catch`. Event topic/data behavior is paired in `event-emitter`, and
  dynamic indexed `bytes`/`string` event topics plus anonymous dynamic events
  are paired in `event-indexed-dynamic`. Free event/error declarations,
  contract-local shadowing, inherited event/error selectors, and named event
  argument ordering are paired in `event-error-shadowing`. Dynamic custom-error
  `string`/`bytes` payloads and tuple-shaped struct error arguments are paired in
  `custom-error-dynamic`. Internal function-pointer
  memory/calldata/storage compatibility,
  external-value memory canonicalization, and location-aware calls are paired
  in `function-type-locations`. Named storage/calldata pointer-return definite
  assignment, modifier continuation, and executable pointer bindings are paired
  in `pointer-return-definite`. Function and modifier override location rules,
  including external memory/calldata canonicalization and pure storage-pointer
  identity, are paired in `override-data-locations`. Inherited callable
  dominance, unrelated multi-base conflicts, bodyless overrides, and overload
  identity are paired in `callable-identity`. Direct and inherited
  address/contract payability conversions are paired in
  `address-contract-conversions`; one-step `address`/`bytes20`/`uint160`
  conversion-category rules are paired in `address-value-conversions`.
  Solidity's current fixed/ufixed declaration-only boundary is paired in
  `fixed-point-boundary`, with static declarations accepted and executable
  fixed-point values rejected against pinned solc.
  Transient library type expressions versus forbidden value-bearing library
  type positions are paired in `library-type-uses`.
  Concrete/library versus interface/abstract `type(T)` code members are paired
  in `type-code-members`.
  Address-only `.balance`/`.code`/`.codehash` receiver rules are paired in
  `address-member-receivers`.
  Type-namespace selectors, bound contract/interface function members,
  scalar one-argument `abi.encodeCall`, and the corresponding forbidden
  library/namespace forms are paired in `function-member-kinds`.
  External function values as ABI words, including address/selector members,
  equality, `abi.encode`, returned function values, pointer calls, and strict
  dirty-padding rejection are paired in `abi-function-values`.
  Malformed ABI input and return-data behavior is paired in `abi-malformed`,
  including permissive dynamic bytes padding/offset behavior, canonical
  `bool`/address/fixed-bytes/narrow-integer checks, generated getters,
  constructors, `abi.decode`, and high-level external returns.
  Storage mapping references are paired in `reference-mapping-storage`,
  including local and nested mapping aliases, mapping members inside storage
  structs, storage-reference rebinding, struct deletion that preserves mapping
  entries, and pinned-solc rejection of direct mapping deletes, memory mapping
  values, storage copies of structs containing mappings, and non-storage
  placements of those structs.
  Uninitialized local storage/calldata pointer definite assignment, delayed
  rebinding, branches, loops, unused declarations, lexical shadowing, and
  storage mutation are paired in `local-pointer-definite`.
  Runtime inheritance-list base-constructor arguments are paired in
  `base-constructor-runtime-args`, including environment reads, file-scope free
  functions, file- and contract-scope `using`, constructor parameters,
  `msg.value`, abstract balances, and abstract external/self calls.
  Nominal Solidity structs with dynamic fields are paired in
  `abi-struct-tuples`, including `abi.encode`, `abi.decode`, round trips, and
  the common typechecker's short-name versus contract-qualified local type
  alias boundary.
  ABI coder mode selection is paired in `abi-coder-modes`, including accepted
  `abicoder v1` dynamic-array ABI behavior and pinned-solc rejection of
  v2-only structs, nested dynamic arrays, struct encoding, and duplicate coder
  pragmas.
  Terminal source outcomes
  are paired in
  `terminal-statements`, including explicit returns, named-return fallthrough,
  revert payloads, and `selfdestruct` halting behavior.
  The checked executable projection keeps the raw checked source around for
  source-to-core elaboration, so source `using` selection is tested before
  user-defined value types erase to primitive words for calls and deployment.
  `scripts/audit_solc_ast_frontend.py` audits every solc `nodeType` in the
  shared source corpus, classifies source-bearing child-field and scalar-field
  positions, checks finite source-scalar value domains, and renders every
  `solc_import` case, so importer gaps are explicit rather than discovered one
  fixture at a time. The frontend treats the whole solc AST as the
  fail-closed ingestion denominator for the pinned 0.8.35 corpus, while the
  Lean semantics only receives the classified abstract Solidity source surface.
  Supported/metadata node kinds, classified source/metadata child fields,
  source scalar fields, and finite source-scalar values are hard gates: adding
  a classified denominator without corpus evidence fails the audit.
- `solidity-interpreter/`: future source-layer replay for shared cases.
- `e2e-proofs/`: reserved for source-semantics claims and audits.

## Rule

Concrete tests may be specific. Source semantics code should stay recursive and
general; if a case exposes a missing rule, add the source-language rule or
record the unsupported Solidity behavior explicitly.
