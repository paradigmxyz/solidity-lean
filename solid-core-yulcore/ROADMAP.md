# Roadmap

## Current Shape

- [x] Small shared `Evm` foundation for 256-bit words and abstract Yul/EVM builtins
- [x] Abstract `FullYul` AST, static checker, and symbolic-value semantics
- [x] Concrete byte-addressed interpreter with explicit Keccak hook
- [x] Complete concrete AST runtime with scoped/forward-visible function
  declarations, object/data sections, immutable byte patching, multi-output
  verbatim, and host hooks for Keccak/verbatim/external effects
- [x] EVM-style memory/storage behavior for active memory size, byte writes, copies, and latest storage writes
- [x] Separate symbolic path executor with path-local side effects
- [x] First concrete/symbolic-to-`FullYul` relation module
- [x] Lean-level builtin claim classification for abstraction boundaries
- [x] Lean-level builtin semantic coverage taxonomy connected to the static checker
- [x] Solidity ABI and storage-layout helper module with symbolic head/tail
  offsets, storage slot expressions, packed-field cursors, and compositional
  storage path steps
- [x] Proof target narrowed to a coevolving sibling-compiler-emittable Yul profile,
  while broader Yul execution remains available as interpreter infrastructure
- [x] Main workspace left untouched; all work stays in the side worktree

## FullYul Track

- [x] Symbolic bytes and symbolic Keccak term algebra
- [x] Named environment declaration, assignment, and block restoration
- [x] Named expression and scoped block evaluator
- [x] Multi-value declarations and assignments
- [x] Fuel-indexed `if`/`switch`/`for`/`break`/`continue`/`leave` semantics
- [x] Function table with parameters, `leave`, multi-result returns, and call assignment
- [x] Yul object/data/code model with symbolic data access
- [x] Broad EVM dialect lifted to symbolic values
- [x] Abstract named AST with checked lexical scopes
- [x] Nested function declaration scope checking

## SymYul Track

- [x] First concrete-byte EVM state and builtin interpreter
- [x] First concrete statement interpreter threading locals, object data, and byte state
- [x] Whole concrete configuration threading `Env`, concrete byte state, functions, and object context
- [x] Symbolic constraints and path-condition simplifier
- [x] Fuel-indexed symbolic expression and statement interpreter
- [x] Symbolic function calls with caller-frame restoration
- [x] Model-guided concrete bridge for symbolic soundness
- [x] Snapshot-aware byte terms and richer external-call event model
- [x] Path-local symbolic EVM side effects in `SymYul` statement execution
- [x] Symbolic pure-builtin result terms for arithmetic and comparisons

## Yul Semantics Roadmap

Primary references:

- Solidity Yul EVM dialect builtins: https://docs.soliditylang.org/en/latest/yul.html
  - Source target pinned to Solidity `0.8.36-develop` documentation, checked
    2026-05-08.
- Ethereum Execution Layer Specification (EELS), for later backend parity:
  https://github.com/ethereum/execution-specs
- Ethereum Yellow Paper, for later backend parity:
  https://ethereum.github.io/yellowpaper/paper.pdf
- EIP-5656 `MCOPY`: https://eips.ethereum.org/EIPS/eip-5656
- EIP-1153 transient storage: https://eips.ethereum.org/EIPS/eip-1153
- EIP-2200/EIP-2929/EIP-3529 storage gas, access lists, and refunds:
  https://eips.ethereum.org/EIPS/eip-2200,
  https://eips.ethereum.org/EIPS/eip-2929,
  https://eips.ethereum.org/EIPS/eip-3529

Target shape: exact Yul AST semantics first, with theorem coverage aimed at the
Yul profile emitted by the sibling Solidity compiler. This profile is expected
to coevolve with that compiler: today it can exclude arbitrary hand-authored Yul
features, but future compiler output such as external calls should be admitted
by extending the accepted profile and its theorem boundary. Broader Yul
constructs may remain executable in the interpreters before they become part of
the verified compiler path. The current external-call extension is a host-effect
profile: it admits calls, logs, creates, and selfdestruct as abstract event/state
summaries rather than exact world-state transitions.

Within the accepted profile, Yul-level control flow, lexical scoping, function
calls, multi-value assignment, storage/memory behavior, and EVM-dialect builtin
behavior should be specified directly over the Yul AST. The EVM-dialect builtins
should be faithful modulo explicit abstractions: gasless execution for now,
symbolic Keccak for proof work, abstract external calls until the sibling
compiler emits them and the verified profile admits them, and no bytecode
stack/PC commitment yet. Exact EVM bytecode semantics belongs to the later
Yul-to-EVM lowering proof.

### Predicted Solidity-Emission Surface

The sibling compiler should target the following Yul surface, in this priority
order. The Lean source of truth is the `SolidityEmission.*` feature predicates
and evidence bundles in `FullYul.lean`; this prose is only the roadmap.

- [x] Current scalar/control/frame output: Yul `let`, multi-`let`, assignment,
  multi-assignment, blocks, sequencing, `if`, `switch`, `for`, `break`,
  `continue`, `leave`, function definitions/calls, scalar word builtins, and
  halt/error builtins. Implemented by canonical AST surface evidence plus
  `ScalarWordBuiltin` and `ControlAndErrorBuiltin`.
- [x] Contract entrypoint and ABI dispatch: selector loading and branching with
  `calldatasize`, `calldataload`, `shr`, `eq`, `lt`, `gt`, `iszero`,
  nonpayable `callvalue` checks, `mstore`, `revert`, `return`, and Yul
  `switch`. Implemented as `AbiDispatchBuiltin`.
- [x] ABI scalar/dynamic memory and returndata handling: memory reads/writes,
  byte writes, `mcopy`, calldata copy/load/size, returndata copy/load/size,
  word arithmetic, shifts, byte/sign extension, `return`, and `revert`.
  Implemented as `AbiMemoryBuiltin`, with ABI head/tail offset helpers in
  `SolidityLayout`.
- [x] Storage layout for state variables, arrays, mappings, structs, packed
  fields, and transient storage: `sload`, `sstore`, `keccak256`, memory
  staging, arithmetic/bit operations, shifts, byte/sign extension, `tload`,
  and `tstore`. Implemented as `StorageLayoutBuiltin`, with symbolic slot,
  mapping, dynamic-array, short/long `bytes`/`string`, and packed-element
  formulas in `SolidityLayout`.
- [x] Deployment, constructors, object data, libraries, and immutables:
  `dataSize`/`dataOffset` AST refs, `datacopy`, `codecopy`, `codesize`,
  `setimmutable`, `loadimmutable`, `linkersymbol`, `memoryguard`, memory
  builtins, `return`, and `stop`. Implemented as `DeploymentBuiltin` plus
  canonical data-ref evidence.
- [x] External calls, events, contract creation, and selfdestruct:
  `call`, `callcode`, `delegatecall`, `staticcall`, `log0`-`log4`, `create`,
  `create2`, `selfdestruct`, returndata builtins, memory builtins, `iszero`,
  and `revert`. Implemented as `ExternalEffectBuiltin`; actual `gas()`-based
  forwarding remains an explicit lowering-environment opt-in.
- [x] Environment, account, and blob queries: context-word builtins plus
  `blockhash`, `balance`, `extcodesize`, `extcodehash`, `extcodecopy`, and
  `blobhash`. Implemented as `EnvironmentQueryBuiltin`.
- [x] Noncanonical escape and lowering lanes: `gas()`/`pc()` are implemented
  only by `LoweringOnlyBuiltin` in the opt-in lowering profile; arbitrary
  `verbatim` is implemented only by `VerbatimEscapeBuiltin` in the opt-in
  verbatim profile. Both are theorem-rejected from canonical
  `currentSolidityEmittable`.
- [ ] Add sibling-repo obligations proving every generated FullYul AST uses the
  corresponding `SolidityEmission.*` feature lane and satisfies
  `currentSolidityEmittable` before the artifact is accepted.

### Phase 1: Pin the Yul Target

- [x] Record the Solidity/Yul documentation version used as the source target.
- [x] Define the accepted AST subset independently of concrete syntax.
- [x] Define a `CompilerEmittable` profile over `FullYul` ASTs that tracks the
  sibling compiler's actual output rather than arbitrary hand-authored Yul.
- [x] Add a canonical aggregate `currentSolidityEmittable` profile for mixed
  Solidity-emittable Yul lanes, excluding arbitrary `verbatim` while admitting
  external calls through explicit host-effect abstractions.
- [x] Admit additional non-verbatim Solidity-emittable EVM-dialect lanes for
  `mcopy`, return-data buffers, code buffers, transient storage, and external
  account/blob queries without widening the older calldata and basic-memory
  runtime wrappers beyond their invariants.
- [ ] Add sibling-repo proof obligations that compiler output satisfies the
  `CompilerEmittable` profile; keep those obligations out of this side worktree
  until the main repo is ready for integration.
- [x] Keep the `CompilerEmittable` profile extensible for future Solidity output
  such as external calls, without prematurely forcing exact world-state semantics
  into the current Yul proof.
- [x] Track builtin signatures so value-producing and statement-only builtins
  are separated at the Yul static-semantics boundary.
- [x] Add the remaining non-verbatim Solidity-emitted EVM-dialect builtins:
  `stop`, `return`, `revert`, `invalid`, `pop`, `sdiv`, `smod`,
  `signextend`, `clz`, `difficulty`, `datacopy`, `setimmutable`,
  `loadimmutable`, `linkersymbol`, and `memoryguard`.
- [x] Keep executable concrete and symbolic support for `verbatim`, including
  multi-output host hooks, outside the accepted compiler-emittable profile.
- [x] Add a guarded `verbatim` profile lane only with explicit call-shape,
  arity, host-effect, and model/provider assumptions.
- [x] Keep `gas()` and `pc()` executable but outside the canonical
  non-deferred Solidity-emittable profile, with an opt-in lowering-environment
  profile lane for compiler output that needs them before backend proof.
- [x] Split every semantic claim into exact-Yul, abstracted-builtin, symbolic,
  or deferred-to-lowering.
- [x] Classify every signatured builtin by the semantic proof lane it belongs to:
  pure word, memory, storage, buffers, object data, halts, host effects, compiler
  builtins, verbatim, or lowering environment.

### Phase 2: Exact Core Yul

- [x] Prove reusable static-checker soundness for variables, scopes, functions,
  loops, `break`, `continue`, and `leave`.
- [x] Prove evaluation-order lemmas for declarations, assignments, multi-assignments,
  expression statements, function calls, switches, and loops.
- [x] Add explicit Yul halting outcomes for `stop`, `return`, `revert`, and `invalid`.
- [x] Prove block-local variables do not escape while outer assignments persist.
- [x] Prove function call frames isolate locals while preserving global builtin state.
- [x] State fuel/divergence assumptions for loops and recursion in theorem statements.

### Phase 3: Faithful EVM-Dialect Builtins

- [x] Keep gas out of the primary Yul semantics until the backend step.
- [x] Prove memory-size, byte-array, word-encoding, zero-length, and overlapping-copy
  laws for the concrete interpreter.
- [x] Prove symbolic memory snapshots are versioned across writes and stable across reads.
- [x] Add byte-level concrete-memory to symbolic-memory-version relation
  preservation before admitting `mload`/word reads to the accepted memory
  profile.
- [x] Add a total calldata-word relation/provider obligation before admitting
  `calldataload` to the accepted buffer profile.
- [x] Prove concrete and symbolic storage latest-write behavior.
- [x] Model storage/transient storage as account-keyed transaction state once calls
  become frame-accurate.
- [x] Treat Keccak as symbolic in proof mode: base semantics has injective
  symbolic hash terms, while concrete collision-freedom is an explicit optional
  model assumption rather than hidden in evaluator equality.
- [x] Treat external calls, creates, logs, and selfdestruct as event/state summaries
  in the host-effect compiler profile until the lowering proof needs exact EVM
  world-state behavior.

### Phase 4: Concrete Interpreter Parity For Yul

- [x] Add an executable concrete runtime that can run accepted Yul ASTs directly,
  including inline and forward-visible function declarations, scoped function
  tables, object/data sections, immutable byte patching, multi-output verbatim,
  memory/storage side effects, and host-provided Keccak/external behavior.
- [x] Prove concrete interpreter results agree with the abstract `FullYul`
  path semantics for the matching concrete execution path.
- [x] Prove the symbolic interpreter is sound for every satisfiable path condition.
- [x] Add concrete fixtures for representative Solidity-emitted Yul snippets,
  without treating fixtures as proof.
- [x] Add loop-summary/invariant support only after the core interpreter relation
  is stable.

### Phase 5: Stack-CFG Backend IR

- [x] Add a stack-oriented CFG target with labels, basic blocks, terminal jumps,
  a target stack, a Lean interpreter, and reflexive/transitive reachability.
- [x] Add the initial source-to-target stack/frame/layout relation and prove
  word/variable expression lowering plus `skip`/expression-statement lowering
  against the concrete Yul evaluator.
- [x] Extend the statement lowering proof to single local declarations,
  including initialized locals and concrete Yul value normalization.
- [x] Extend the statement lowering proof to local assignment with explicit
  stack-frame replacement and duplicate-free layout assumptions.
- [x] Add a compositional two-statement sequencing combinator that threads the
  first statement's output layout into the second and proves appended CFG code.
- [x] Integrate nested sequencing into a fuel-bounded statement compiler for the
  currently admitted straight-line statement forms.
- [x] Extend the statement lowering proof to blocks, including block-local
  stack-slot popping and outer-layout restoration.
- [x] Wrap the proved linear statement compiler in the multi-block `CfgCodegen`
  boundary so straight-line fragments and control-flow fragments share a target
  theorem shape.
- [x] Add the first explicit control-flow slice for `if`, with a conditional
  terminal branch, CFG reachability proof, and layout-preserving branch join.
- [x] Add the first `switch` control-flow slice for one case without a default,
  including equality branching, discriminator popping, and fallthrough.
- [x] Extend the one-case `switch` slice to default bodies with both branches
  proved against the same layout-preserving join.
- [x] Add the first chained multi-case `switch` slice for two cases without a
  default, preserving the discriminator across tests and popping it only at the
  selected/fallthrough path.
- [x] Extend the two-case `switch` slice to default bodies with all three
  destination paths proved against a common layout-preserving join.
- [x] Add a public `compileCfgStmtFrom` dispatcher theorem over every currently
  proved Stack-CFG statement slice: linear statements, `if`, and fixed
  one/two-case switches.
- [x] Add the first compositional control-exit destination slice for `break`,
  `continue`, and `leave`, proving each jumps to caller-provided labels while
  preserving the stack/frame relation.
- [x] Add the first open-exit CFG theorem with arbitrary continuation labels
  for `if`, moving from closed `halt` wrappers toward fragment-style control
  flow.
- [x] Add the open-exit straight-line/basic-block theorem, proving compiled
  linear code reaches an arbitrary continuation label and can serve as the
  leaf case for compositional CFG fragments.
- [x] Add the first open-exit `switch` theorem for a one-case/no-default
  branch, proving discriminator preservation through the test and cleanup at
  both selected and fallthrough destinations.
- [x] Extend the open-exit one-case `switch` theorem to default bodies,
  proving both the selected case and default case reach the same arbitrary
  continuation label.
- [x] Add the first loop CFG fragment theorem for the condition-false path,
  including pre-loop code, arbitrary loop/cleanup/exit labels, and verified
  cleanup of pre-loop locals back to the outer layout.
- [x] Add an open-exit chained two-case/no-default `switch` theorem, preserving
  the discriminator across the second test and proving selected/fallthrough
  cleanup to an arbitrary continuation label.
- [x] Extend the open-exit chained two-case `switch` theorem to default bodies,
  proving every selected/default branch reaches the same arbitrary
  continuation label.
- [x] Add CFG-composition foundations for label freshness, program extension,
  appended block lookup, and one-step reachability preserved by extension.
- [x] Lift straight-line open-exit statement correctness through
  `Program.Extends`, proving a compiled basic block remains correct inside a
  larger CFG that preserves its entry block.
- [x] Add an open-entry control-exit theorem for `break`, `continue`, and
  `leave`, so loop/function contexts can choose the entry and destination
  labels for abrupt exits.
- [x] Lift open-exit `if` correctness through `Program.Extends`, proving branch
  fragments remain correct inside larger CFGs that preserve their entry/body
  blocks.
- [x] Lift open-entry control-exit correctness through `Program.Extends`,
  proving abrupt-exit jumps remain correct inside larger loop/function CFGs.
- [x] Lift one-case/no-default open-exit `switch` correctness through
  `Program.Extends`, covering selected and fallthrough branches inside larger
  CFGs.
- [x] Lift one-case/default open-exit `switch` correctness through
  `Program.Extends`, covering selected and default branches inside larger CFGs.
- [x] Lift two-case/no-default open-exit `switch` correctness through
  `Program.Extends`, covering first match, second match, and fallthrough inside
  larger CFGs.
- [x] Lift two-case/default open-exit `switch` correctness through
  `Program.Extends`, covering first match, second match, and default inside
  larger CFGs.
- [x] Add basic label-supply helpers for future arbitrary switch lowering,
  including allocated label ranges, next-label computation, range bounds, and
  a proof that the next label is fresh from the allocated range.
- [x] Add the first executable arbitrary chained-switch lowering surface:
  `SwitchCaseCode`, generic switch-chain CFG builders, arbitrary case/default
  compilation helpers, and three-case fixtures.
- [x] Add reusable arbitrary switch-chain proof bricks: case/default compiler
  destructors plus target-only entry, miss, first-case lookup, and first-case
  reachability lemmas for generated switch fragments.
- [x] Add prefix/suffix program-extension lemmas for fresh blocks and
  target-only head lookup/match/miss lemmas for generated switch tail-test
  chains.
- [x] Add generated-label freshness/range lemmas for arbitrary switch case
  blocks and tail-test blocks, covering labels before each generated range and
  labels at or after each generated range.
- [x] Prove generated arbitrary switch fallback lookup for the automatic label
  layout under the intended `entry < caseLabelStart` discipline.
- [x] Prove generated arbitrary switch fallback execution to the join,
  including pop-only no-default fallback and default-body fallback helpers.
- [x] Add the first source-to-Stack-CFG preservation theorem for the arbitrary
  switch-chain compiler path: empty `switch` with no default through
  `compileSwitchChainFrom`.
- [x] Extend arbitrary switch-chain source preservation to singleton
  no-default switches through `compileSwitchChainFrom`, covering selected-case
  and no-match fallback paths.
- [x] Extend arbitrary switch-chain source preservation to singleton/default
  switches through `compileSwitchChainFrom`, covering selected-case and
  default-body fallback paths.
- [x] Extend arbitrary switch-chain source preservation to two-case/no-default
  switches by proving the generated two-case chain extends the already-proved
  fixed two-case CFG.
- [x] Extend arbitrary switch-chain source preservation to two-case/default
  switches by proving the generated two-case/default chain extends the
  already-proved fixed two-case/default CFG.
- [x] Add a recursive target-only all-miss theorem for generated switch
  tail-test chains, usable inside larger CFGs via `Program.Extends`.
- [x] Lift generated switch test blocks into the full auto switch CFG and prove
  arbitrary all-miss entry execution reaches the generated fallback label.
- [x] Connect concrete Yul no-match switch selection to the compiled
  `switchCaseCodesMiss` predicate for arbitrary generated switch cases.
- [x] Prove the arbitrary no-default/no-match generated switch path preserves
  concrete Yul semantics through fallback cleanup and join reachability.
- [x] Prove the arbitrary default/no-match generated switch path preserves
  concrete Yul semantics by routing through fallback and executing the compiled
  default body.
- [x] Add recursive selected-case proof bricks for generated switch tails,
  including case-block preservation and body execution to the join.
- [x] Lift selected-case execution through the generated switch entry block,
  proving arbitrary selected-case routing from entry to join under
  `Program.Extends`.
- [x] Connect concrete Yul selected-case evaluation to generated
  `SwitchCaseCodesExec` witnesses and prove arbitrary selected-case source
  preservation to the join.
- [x] Prove arbitrary no-default generated switch source preservation by
  dispatching between selected-case and no-match paths.
- [x] Prove arbitrary default generated switch source preservation by
  dispatching between selected-case and default-no-match paths.
- [x] Add the public generic `compileSwitchChainFrom` theorem covering
  arbitrary case lists with optional defaults.
- [x] Route the public `compileCfgStmtFrom` dispatcher through the generic
  closed switch-chain compiler, removing the one/two-case switch cap from the
  accepted dispatcher path.
- [x] Add the first full cyclic `for` lowering accepted by the public
  dispatcher, covering arbitrary iterations when pre/body/post compile through
  the straight-line subset and body/post preserve the loop layout.
- [x] Add a small open-control-context dispatcher theorem for straight-line
  statements and `break`/`continue`/`leave`, relating normal flow to a join
  label and abrupt flow to caller-provided destinations.
- [x] Add the first open `if` theorem that composes through the open dispatcher,
  covering straight-line bodies and direct abrupt exits without bespoke nested
  `if`/exit proof cases.
- [x] Add a one-level public open dispatcher covering open `if` plus the
  straight-line/control-exit open cases behind a single theorem.
- [x] Add the first recursive open-control compiler with label supply,
  preserving nested `if` composition over straight-line statements and direct
  control exits.
- [x] Extend the recursive open-control compiler with straight-line-prefix
  sequencing into recursive open continuations.
- [x] Add reusable recursive open-control label-supply/freshness invariants for
  future composition of multi-block fragments.
- [x] Add compiler-only layout well-formedness invariants for straight-line and
  recursive open-control fragments.
- [x] Add layout-aware exit targets and same-layout exit-correctness adapters
  for current open-control fragments.
- [x] Add compositional sequence outcome lemmas for layout-aware exits and
  concrete Yul sequence evaluation.
- [x] Add verified uninitialized `letMany` stack-frame extension to the
  straight-line compiler.
- [x] Add pure expression-list stack compilation and preservation lemmas
  supporting initialized `letMany` and future multi-assignment lowering.
- [x] Add verified initialized `letMany` lowering for pure expression lists.
- [x] Add verified pure-expression multi-assignment lowering with source-order
  stack evaluation and layout-indexed stores.
- [x] Add verified no-op function-definition lowering for the current
  concrete-statement evaluator.
- [x] Bridge the straight-line compiler theorem to `evalProgramStmtFuel` for
  statements accepted by `compileStmtFrom`.
- [x] Bridge two-statement straight-line sequencing to `evalProgramStmtFuel`.
- [x] Bridge fuel-bounded straight-line statement and block compilation to
  `evalProgramStmtFuel`/`evalProgramBlockFuel`.
- [x] Add CFG-level `Reaches` theorems for the fuel-bounded program-evaluator
  bridge.
- [x] Add a public dispatcher-level program-evaluator theorem for the current
  linear, `if`, `switch`, and loop Stack-CFG slices.
- [x] Add first function-call lowering proof bricks: stack-frame removal under
  preserved return temporaries plus caller-frame restoration facts for program
  and runtime Yul function calls.
- [x] Add call-assignment cleanup proof bricks for return-slot duplication,
  offset stores into the caller frame, and callee-frame removal.
- [x] Add call-declaration cleanup and function-entry layout proof bricks tying
  return-slot locals and param/return frames to Yul `declareMany?` and
  `initFunctionEnv`.
- [x] Add call setup proof bricks showing compiled argument evaluation plus
  zero return slots builds the callee entry `StackRel` above the caller frame.
- [x] Add the first call-parametric CFG terminal layer with `CallSem`,
  `Term.call`, call-aware stepping/reachability, and call-free compatibility
  lemmas.
- [x] Add the first call-aware `assignCall` Stack-CFG theorem, proving compiled
  arguments feed `CallSem` and returned values are stored back into the caller
  frame for arbitrary arity under the abstract call-correctness assumption.
- [x] Add a public call-aware Stack-CFG dispatcher wrapper that routes
  `assignCall` through the call terminal and reuses all call-free statement
  proofs under `ReachesWithCalls`.
- [x] Add call-aware `letCall` lowering, including a proved return-segment
  reversal so source-order call returns become `declareMany?` frame order in
  the extended layout.
- [x] Add a compiled-function-table proof brick for named return extraction:
  compiling return locals reads `valuesForNames?` in source order and pushes
  the corresponding words on the target stack.
- [x] Add a compiled-function-body finalization brick that appends a
  return-extraction block to an open CFG body and proves routed normal/leave
  execution reaches halt with source-ordered return words on top.
- [x] Prove open-recursive and function-finalizer CFG output is call-free, then
  lift the function-body finalization theorem to call-aware reachability.
- [x] Add an explicit compiled-function wrapper for Yul function definitions
  and prove the wrapped body inherits call-free, return-finalizer, and
  call-aware reachability correctness.
- [x] Add a compiled-function environment coverage relation and prove
  table-covered function bodies inherit call-aware correctness without yet
  tying recursive calls to the compiled table.
- [x] Bridge open-recursive function-body compilation to the concrete
  `evalProgramStmtFuel` evaluator, then lift function wrapper and table
  coverage correctness to that program-evaluator boundary.
- [x] Add an `evalFunctionFuel` bridge showing a successful source function
  call exposes a table-covered compiled body run with matching return-value
  extraction and caller-environment restoration.
- [x] Add a `CompiledCallSemRealizesBelow` boundary proving an abstract
  `CallSem` provider backed by source correctness and compiled-table coverage
  also realizes a matching compiled function-body run.
- [x] Add an open `assignCall` CFG leaf that calls through `CallSem`, stores
  returned values into the caller frame, and jumps to an arbitrary
  continuation label.
- [x] Add an open `letCall` CFG leaf that calls through `CallSem`, reverses the
  returned segment into declaration order, extends the caller frame, and jumps
  to an arbitrary continuation label.
- [x] Add a one-level call-aware open dispatcher that composes open `letCall`
  and `assignCall` leaves with the existing call-free open compiler under
  call-aware reachability.
- [x] Add monotonic and object-indexed/contextual call-provider predicates,
  making the current state-only `CallSem` boundary explicit before the
  compiled-table tie-the-knot.
- [x] Add compiled-function run scaffolding for provider realization:
  source/target initial configurations, source-order return extraction, and
  checked `StackRel`/result-extraction proof bricks.
- [x] Prove that a table-covered successful source `evalFunctionFuel` call
  yields a concrete `FunctionRunWithCalls` witness from the compiled entry to
  extracted source-order returns.
- [x] Add argument-normalization lemmas so compiled function-run witnesses line
  up with the normalized argument words consumed by CFG call terminals.
- [x] Add a run-aware call-provider realization predicate tying source-correct
  `CallSem` answers to compiled `FunctionRunWithCalls` witnesses below fuel.
- [x] Prove the state-only call-provider ABI for source-backed calls at a
  fixed object/context by showing `evalFunctionFuel` is insensitive to the
  caller's local environment for returned values and state.
- [x] Add an executable compiled-function environment compiler and prove
  successful table compilation implies `CompiledFunctionEnvCovers`.
- [x] Add executable-table wrappers that produce `FunctionRunWithCalls` and
  call-realization predicates directly from successful function-env compilation.
- [x] Add object-indexed compiled-call realization predicates and constructors
  so fixed-object source-backed calls connect to compiled tables without a
  global object-insensitive `CallSem` assumption.
- [x] Refactor call-aware statement dispatcher proofs around per-source-config
  call correctness, with global/object/source-backed provider wrappers.
- [x] Add source-backed compiled-table realization constructors for both
  compiled-body runs and extracted `FunctionRunWithCalls` witnesses.
- [x] Add the first executable Stack-CFG instruction-list stack-depth checker
  with composition and stack-shuffle depth proofs for pop/drop/dup/reverse code.
- [x] Prove expression-code stack-depth effects for single expressions,
  expression lists, source-order expression lists, return extraction, and
  expression statements.
- [x] Prove assignment-store and call-cleanup stack-depth effects for source-order
  stores, offset stores, call assignment cleanup, and call declaration cleanup.
- [x] Prove straight-line statement and call-setup stack-depth effects for
  zero init, layout extension, `let`, assignment, `compileStmtFrom`,
  `compileSeqFrom`, and argument/return-slot setup.
- [x] Prove fuel-bounded statement/block stack-depth effects, using layout
  prefix extension to justify block-local cleanup pops.
- [x] Add terminal/block stack-depth checking and prove open call-entry,
  assign-call return, and let-call return blocks satisfy it.
- [x] Prove function return-finalizer block stack-depth admission for compiled
  function bodies.
- [x] Lift function return-finalizer block-depth admission through compiled
  function records.
- [x] Add label-target-aware stack-depth checking for CFG terminals, and prove
  linear and open call blocks satisfy their successor-label depth contracts.
- [x] Prove target-aware branch-entry stack-depth admission for open `if`
  lowering.
- [x] Prove target-aware switch discriminator, selected-case, and miss-cleanup
  block stack-depth bricks.
- [x] Add the first program-level stack-depth admission predicate and prove it
  for linear statement programs.
- [x] Prove program-level stack-depth admission for open `assignCall` and
  `letCall` CFG fragments.
- [x] Prove compositional program-level stack-depth admission for open `if`
  CFG fragments.
- [x] Add reusable program-level stack-depth composition for appended CFG
  fragments.
- [x] Prove program-level stack-depth admission for fixed one/two-case open
  `switch` CFG fragments, with and without defaults.
- [x] Add generated-switch fallback, case-block-list, and tail-test-list
  stack-depth admission bricks for arbitrary switch-chain lowering.
- [x] Prove explicit generated switch-chain program-level stack-depth
  composition from entry, case, test, fallback, and join label depths.
- [x] Lift generated switch-chain stack-depth admission through
  `switchChainAutoToProgram` and `compileSwitchChainFrom`.
- [x] Prove program-level stack-depth admission for the closed linear `for`
  loop CFG and its `compileForLoopLinearFrom` wrapper.
- [x] Add compositional function-body return-finalizer and compiled-function
  environment stack-depth predicates.
- [x] Prove jump-only control-exit and basic open-statement compiler
  program-depth admission.
- [x] Add recursive open-body program-depth composition bridges for nested
  `if` and sequencing fallback fragments.
- [x] Lift open call-aware `assignCall`/`letCall` leaves through
  `compileCfgStmtOpenWithCallsFrom` at the program-depth boundary.
- [x] Lift the one-level open-statement dispatcher through program-depth
  admission for open `if` plus basic open-statement leaves.
- [x] Add closed/public linear, `if`, `assignCall`, and `letCall` CFG
  program-depth admission wrappers.
- [x] Add closed generic switch-chain program-depth admission through
  `compileSwitchChainClosedFrom`.
- [x] Lift closed and call-aware public statement dispatchers through
  program-depth admission.
- [x] Add one-step and auto-label recursive open-statement program-depth
  dispatchers, composing `if`, `seq`, and basic open leaves.
- [x] Lift function-body and function-definition program-depth wrappers through
  the recursive open-statement dispatcher.
- [x] Lift compiled function-environment program-depth checking through the
  per-function open-recursive depth wrappers.
- [x] Package recursive open/function/function-environment depth assumptions
  behind compositional obligation structures while preserving compatibility
  wrapper theorem names.
- [x] Add a layout-carrying flow-to-exit target abstraction for future
  distinct normal/abrupt destination layouts.
- [x] Add generic pop-and-jump cleanup correctness for exits from an extended
  stack layout back to a suffix target layout.
- [x] Prove layout-aware abrupt control exits can use cleanup jumps to reach a
  `ControlCtx` target with its own stack layout.
- [x] Prove stack-depth admission for cleanup jumps and layout-aware
  abrupt-exit cleanup fragments.
- [x] Add an executable cleanup-exit compiler wrapper with semantic correctness
  and program-depth admission theorems.
- [x] Lift layout-aware cleanup-exit correctness through `Program.Extends` for
  composition into larger CFG fragments.
- [x] Add same-layout/no-local compatibility equations connecting cleanup-exit
  compilation back to the existing open control-exit compiler branch.
- [x] Add cleanup-exit compiler destructors and lookup-freshness lemmas for
  future recursive/open-control composition.
- [x] Add a context-aware open-leaf compiler bridge with semantic, freshness,
  call-free, and program-depth theorems.
- [x] Add target-layout-derived cleanup slot computation for abrupt exits with
  proof hooks for semantic and stack-depth composition.
- [x] Add function-return and loop-target `ControlCtx` constructors preserving
  outer `leave` while installing loop-local `break`/`continue` targets.
- [x] Add an auto-cleanup context-aware open-leaf compiler bridge that derives
  target-specific cleanup slots and preserves the old same-layout API.
- [x] Add a flexible normal-layout correctness theorem for auto-cleanup open
  leaves, so abrupt-only branches can compose under a caller-chosen fallthrough
  layout.
- [x] Add the first context-aware `if` lowering slice, composing false
  fallthrough with true-branch auto-cleanup exits without special nested cases.
- [x] Add a one-level context-aware open-statement dispatcher that composes
  auto-cleanup leaves with context-aware `if` lowering.
- [x] Add a compositional one-level sequence CFG combinator with append
  freshness, normal no-halt, and exit-correctness theorems for `stmt₁; stmt₂`.
- [x] Expose a one-level-or-sequence context-aware dispatcher with call-free
  and exit-correctness theorems.
- [x] Add the recursive context-aware open-statement compiler skeleton for
  nested `if`/`seq` with call-free, monotone label-supply, and out-layout
  well-formedness invariants.
- [x] Prove recursive context-aware label-freshness intervals and
  exit-correctness for nested `if`/`seq`, carrying normal no-halt preservation
  through the same compositional induction.
- [x] Add a same-layout context-aware function-body return finalizer using
  `ControlCtx.functionReturn`, proving normal/`leave` exits reach return-value
  extraction without admitting direct `break`/`continue`, and bridge the
  theorem to the program evaluator used by call-aware function-table proofs.
- [x] Add a same-layout context-aware function-definition compiler wrapper with
  call-free, evaluator-bridge, and direct/program call-aware correctness
  theorems.
- [x] Add same-layout context-aware compiled-function table coverage and a
  table-level body-program correctness theorem for successful compiled entries.
- [x] Add the first context-aware open-loop CFG builder using loop-local
  `ControlCtx` targets for `break`/`continue`, with call-free and monotone
  label-supply and interval-freshness theorems.
- [ ] Extend layout-aware destination handling into loops, functions, and
  flow-sensitive nested exits with distinct normal/abrupt layouts.
- [ ] Before EVM lowering consumes Stack-CFG programs, add `Program.WF` with
  label uniqueness, branch-target closure, generated-label freshness/ranges,
  max-stack bounds, and label-to-layout checking beyond raw stack depth.
- [x] Add compiled-function tables, returns, stack-shuffle checking, and
  stack-depth admission.
- [ ] Connect Stack-CFG state/effects to the broader `FullYul` accepted-profile
  relation rather than only the concrete AST slice.

### Phase 6: Later Yul-To-EVM Lowering

- [ ] Choose an explicit EELS fork only when lowering to bytecode begins.
- [ ] Add stack, PC, bytecode, gas, access-list, refund, and exceptional-halt semantics
  in the EVM target model.
- [ ] Prove gas-free Yul builtin semantics refines to the EVM model where execution
  does not halt exceptionally.
- [ ] Add exact gas/refund/access-list claims separately from the gasless Yul semantics.
- [ ] Differential-test generated bytecode snippets against EELS as evidence, while
  keeping Lean refinement the proof boundary.

### Definition of Done

- [x] `lake build` is green.
- [x] Placeholder scan has no `sorry`, `admit`, custom `axiom`, `unsafe`, or `partial`.
- [x] Every Yul AST form accepted by the compiler-emittable profile has
  static-checker and evaluator theorem coverage.
- [x] Every EVM-dialect builtin accepted by the compiler-emittable profile has an
  arity/result signature and a theorem for its gasless Yul-level effect or
  explicit symbolic abstraction.
- [x] Concrete and symbolic interpreters are related to `FullYul` by named theorems.
- [x] Broad executable interpreter support beyond the compiler-emittable profile is
  clearly marked as interpreter coverage, not part of the current verified
  compiler theorem.
- [x] The later Yul-to-EVM proof owns stack, PC, bytecode, gas, refunds, access lists,
  and exact EVM exceptional halting.
- [x] Remaining differences from exact EVM bytecode semantics are listed as deferred
  backend proof obligations, not hidden in Yul examples.
