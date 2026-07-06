# Roadmap

## Solidity Source Refactor For Future Yul Target

- [x] Start a new `$verifiable-compiler` goal for source-semantics refactoring
      only, explicitly excluding Solidity-to-Yul compiler implementation.
- [x] Identify the intended Nethermind Yul target shape from PR #84,
      `Align Yul interpreter with Solidity semantics`: `EvmYul.Yul.exec`,
      `eval`, `evalValues`, `call`, and `primCall` over `EvmYul.Yul.State`,
      with block-scope cleanup, declaration/assignment separation,
      unknown/duplicate variable errors, zeroed function returns,
      reverted-call-as-failed-call behavior, right-to-left argument evaluation,
      selected-case switch execution, omitted-default-as-empty switch notation,
      and halting `SELFDESTRUCT`.
- [x] Use `/Users/dan/Projects/evm-compiler` as proof-architecture context,
      especially its repaired source-owned layers, explicit outcome
      observations, source-fuel recursion boundaries, and avoidance of public
      layout/replay/callback evidence.
- [x] Add a first Solidity source observation facade: source events project to
      target-shaped log entries by address/topics/data, and statement/call
      results project to observation records without exposing compiler
      lowering artifacts.
- [x] Audit the Solidity source runtime interface for any remaining
      compiler-shaped names that should be rephrased as source-owned
      environments, observations, or explicit host-oracle boundaries.
- [x] Factor relation-ready source observations for storage, transient
      storage, logs, selfdestruct effects, returns, reverts, and external
      oracle interactions while preserving the rich Solidity source state.
- [x] Keep the first source-observation refactors guarded by raw and checked
      source examples: event/log projection, low-level-call observations, and
      contract-creation observations.
- [x] Split statement-level runtime observation from internal memory-layout
      instrumentation: `RuntimeObservation` exposes source locals, source heap
      objects, and abstract allocation sizes, while byte-addressed memory
      contents and free-pointer details remain internal diagnostics rather than
      the future preservation interface.
- [x] Add source-owned `StorageLayoutObservation` and
      `StorageFieldObservation`, exposing typed storage layout shape, slot
      span, source slot, packing metadata, and transient status for future
      storage preservation without replacing Solidity storage with target EVM
      state.
- [x] Add `StorageFieldWordObservation` so packed/transient source storage
      field loads and stores expose before/after source slot words and field
      words, leaving compiler proofs responsible for relating those source
      words to target `sload`/`sstore` code.
- [x] Add `StoragePathResolutionObservation` so mapping, struct, dynamic-array,
      fixed-array, and `bytes` source paths expose the resolved source slot,
      resolved typed layout, or source revert reason before any future Yul
      storage-address code is chosen.
- [x] Add an ABI-entry observation boundary: `AbiCallResult.observe` projects
      call success, normalized output bytes, and abstract observed source state
      without exposing Yul memory, stack layout, or Solidity-to-Yul lowering.
- [x] Add `AbiEntryObservation` for source ABI execution entries, exposing
      fuel, calldata/msg fields, base context, call context, submitted state,
      execution state, and optional result for both message-call and
      transaction wrappers, including source-visible transient-storage
      clearing without introducing target lowering.
- [x] Add `AbiDispatchObservation` to ABI entries, exposing the source
      selector/receive/fallback dispatch decision, selected source function
      metadata, and decoded source arguments for future dispatcher
      preservation, without introducing generated Yul dispatch code.
- [x] Nest the selected `FunctionEntryObservation` inside ABI-entry
      observations when dispatch selects a source function, so ABI
      preservation can relate decoded arguments and source function execution
      before ABI return/revert encoding.
- [x] Add `AbiResultEncodingObservation` to ABI-entry observations, relating
      nested source function returns/reverts to the ABI `success` flag and
      encoded output bytes without exposing target memory offsets or generated
      return/revert code.
- [x] Add `FunctionEntryObservation` for source function/deployment entries,
      including ordinary selector-bearing function runs and constructor runs
      with `construction := true`, submitted state, initial parameter frame,
      source call context, and final call observation, so function-call and
      deployment preservation have source-owned boundaries before any Yul
      relation exists.
- [x] Extend `FunctionEntryObservation` with the pre-normalization source
      body result so terminal causes such as `selfdestruct` remain visible
      before Solidity call results normalize them for the caller boundary.
- [x] Add `FunctionExitObservation` to make Solidity function-exit
      normalization explicit: fallthrough and bare returns collect named
      return variables, explicit return values are coerced, reverts roll back
      to the submitted state, invalid control exits revert, and
      `selfdestruct` becomes an empty successful call result.
- [x] Add `FunctionReturnInitializationObservation` to expose source return
      variable defaulting and accepted-entry initial runtime for later relation
      to Yul's zeroed function return variables.
- [x] Add `SourceUnitDeploymentObservation` for whole-program deployment
      entries, packaging the resolved source interface, selected contract name,
      deployment `self`/sender/value, constructor arguments, source
      construction context, nested constructor entry, and final source call
      result without choosing object installation, bytecode layout, or a Yul
      creation dispatcher.
- [x] Add `SourceUnitDeploymentAbiObservation` for constructor calldata entry,
      making constructor parameter types, ABI-decoded source arguments,
      malformed-calldata failure, nested deployment observation, and final
      source result explicit before any Yul creation-code relation exists.
- [x] Add `ContractCallObservation` for source contract-level dispatch,
      exposing target resolution, selected function metadata, message-call
      versus transaction execution state, nested function-entry observation,
      and final source call result without introducing target dispatch code.
- [x] Remove the orphan `SolidCore.Solidity.ControlCore` source-to-core compile
      shim and rename checked/source witnesses that described source
      elaboration as "lowering".
- [x] Factor local runtime observation into `LocalObservation`, exposing source
      frames, current frame, and source-visible bindings with shadowing already
      resolved by source lookup rather than by stack slots or target layout.
- [x] Add source-owned local declaration and assignment observations,
      separating initializer/RHS effects, declaration/defaulting, assignment
      writes, unknown-local failures, and final source locals for later
      relation to Yul `VarStore` declaration/assignment behavior.
- [x] Add `BlockScopeObservation` for source block-scope entry/exit,
      exposing pushed scope, body result, and popped final result so the later
      Yul `VarStore` block-cleanup relation has a Solidity-owned boundary.
- [x] Add `EvalObservation` for source statement evaluation results, making
      completed execution versus fuel exhaustion explicit at the source
      observation boundary.
- [x] Add `IfBranchObservation` for source conditional branch selection,
      exposing condition effects, selected branch, and branch result for later
      relation to Yul `if`/`switch` control preservation.
- [x] Add `SwitchBranchObservation` for source switch branch selection,
      exposing discriminant effects, selected case/default/omitted-default
      behavior, and branch result for later relation to Yul `switch`
      preservation.
- [x] Add `WhileLoopObservation` for source while-loop control,
      exposing condition effects, first body result, break/continue handling,
      and final source result for later relation to Yul loop preservation.
- [x] Add `DoWhileLoopObservation` for source do-while control,
      exposing body-before-condition ordering, break/continue handling, and
      final source result for later relation to Yul loop preservation.
- [x] Add `ForLoopObservation` for source for-loop control,
      exposing loop-scope entry, initializer, condition/body/post outcomes,
      break/continue handling, and final scope cleanup for later relation to
      Yul loop preservation.
- [x] Add `ExprListEvaluationObservation` for Solidity child-expression list
      evaluation, exposing the effective Yul-compatible order, preserved
      result positions, input/output runtimes, and revert data for later
      relation to Nethermind Yul `evalValues`.
- [x] Add `ChildEvaluationPolicyObservation` and thread it through expression
      list observations, making Solidity's unspecified sibling-expression
      policy explicit: an absent source order uses the Nethermind
      Yul-compatible deterministic order, while explicit test contexts remain
      observable.
- [x] Add `LowLevelCallEvaluationObservation` for source low-level call
      expressions, exposing the source operand list, effective child-evaluation
      policy, parsed `{gas,value}` option-order metadata, decoded call request,
      abstract host/precompile resolution, returned `(bool, bytes)` value, and
      output runtime trace without introducing Solidity-to-Yul lowering.
- [x] Add `ContractCreationEvaluationObservation` for source `new`
      expressions, exposing constructor-argument/value/salt operand evaluation,
      effective child-evaluation policy, abstract creation resolution, returned
      address or revert data, and successful creation trace without modeling EVM
      deployment layout or generating Yul.
- [x] Add `TryExternalCallEvaluationObservation` for source `try`
      external-call statements, exposing operand sequencing, decoded call
      request, missing-code fallback, abstract call resolution, ABI return
      binding, catch matching, and final statement result without generating
      Yul dispatch code.
- [x] Add `TryContractCreateEvaluationObservation` for source `try new`
      statements, exposing constructor/value/salt operand sequencing,
      abstract creation resolution, created-address binding, catch matching,
      and final statement result without modeling deployment byte layout or
      generating Yul dispatch code.
- [x] Add `TerminalEvaluationObservation` for source terminal statements,
      exposing return values, abstract revert payloads, source child-evaluation
      policy, and selfdestruct account effects as Solidity-layer outcomes
      without lowering them to stack, memory, or Yul control-flow layout.
- [x] Add `BinaryArithmeticObservation` so checked and unchecked Solidity
      arithmetic exposes source operand mode, primitive result, and
      overflow/div-by-zero/type panic outcomes before any future relation to
      generated Yul arithmetic/check code.
- [x] Add a Forge/solc versus Solidity-interpreter harness, modeled after the
      `evm-compiler` Forge comparison scripts, so source-semantics witnesses
      can be paired with ordinary Forge tests until a concrete Solidity parser
      or solc-AST importer lets both lanes consume the same `.sol` source.
- [x] Add the first solc-AST importer lane to the Forge/interpreter harness:
      the checked-arithmetic case now tests a shared `.sol` contract with
      Forge and imports the same contract's solc-emitted Solidity AST into the
      Lean source AST for interpreter checks.
- [x] Pivot the solc-AST importer from ad hoc fixture growth to a
      coverage-driven whole-AST frontend: every solc `nodeType` seen in the
      shared source corpus is classified as supported, explicitly out of scope
      (`ImportDirective`, inline assembly/Yul), or unimplemented, and the
      manifest-wide audit must stay green before adding future source syntax.
      The audit also renders every `solc_import` case, so a supported node
      cannot hide in an unhandled source-unit, contract, declaration, or
      expression position.
- [x] Extend the solc-AST importer from selected contract bodies to whole
      source-unit declaration rendering: pragmas, free functions/constants,
      free events/errors/types, contract-local struct/enum/user-value-type and
      `using` declarations, fixed-array type names, and solc type-expression
      identifiers now round-trip through a shared source-declarations `.sol`
      case with Forge/solc and the Lean source interpreter.
- [x] Tighten the solc-AST frontend toward a whole-AST boundary by separating
      metadata nodes from rendered source nodes, rendering `FunctionTypeName`
      and `OverrideSpecifier`, preserving unit-denominated, hex-string,
      unicode-string, and address literals, and failing on unrendered
      source-unit/contract children. The executable projection also keeps
      bodyless inherited abstract declarations as interface/override evidence
      rather than requiring core code for them. The shared frontend-frontier
      `.sol` case checks structured docs-as-metadata, overrides,
      explicit override base lists, function-valued external calls/equality,
      constant-expression static array lengths, and literal forms without
      adding Solidity-to-Yul lowering.
- [x] Strengthen the solc-AST frontend audit from node-kind and render
      coverage to child-field shape coverage: every source-bearing AST child
      position seen in the shared corpus is classified as source, metadata, or
      unclassified, and unclassified positions fail the importer/audit before
      they can silently disappear from the abstract Solidity source layer.
      The audit reports classified-versus-seen source and metadata child
      fields, and the frontend-frontier case now covers every classified
      source child-field position for the pinned solc 0.8.35 corpus, including
      modifier override specifiers and `using {f}` function-list entries.
- [x] Extend the solc-AST frontend audit to scalar field positions, so
      source-bearing scalars such as names, visibility, mutability, operators,
      literal values, named-argument lists, and inline-array markers are
      distinguished from solc analysis metadata and parser metadata. The audit
      now fails on unclassified scalar fields and the importer preserves
      solc's `address payable` spelling from `ElementaryTypeName.stateMutability`
      while keeping the Solidity layer abstract.
- [x] Add finite-domain value checks for source scalar fields, so unexpected
      solc spellings for operators, function kinds, contract kinds,
      visibilities, mutabilities, literal kinds, unit denominations,
      tuple/using flags, and catch names fail the frontend audit. The
      frontend-frontier case now also covers interface contract kind,
      anonymous events, private functions, using-operator/global directives,
      immutable and transient state declarations, storage local references,
      all source assignment/binary operator spellings, and all unit
      denominations in the pinned 0.8.35 finite-domain denominator.
- [x] Make the whole-AST frontend audit's classified denominators hard gates:
      supported node kinds, metadata node kinds, classified source child
      fields, metadata child fields, source scalar fields, and finite
      source-scalar values now fail the audit when they are declared but unseen
      in the shared solc 0.8.35 corpus.
- [x] Close the checked executable projection gap for the whole-AST frontend:
      checked execution now keeps the raw checked source unit available for
      core elaboration, so `using`/operator selection happens before
      user-defined value types erase to primitives. The source-core projection
      also threads file-level user-value types, enums, and structs into the raw
      source type environments, and the frontend-frontier case executes the
      scalar operator/unit frontier without adding Solidity-to-Yul lowering.
- [x] Align constructor/deployment elaboration with the same source boundary:
      constructor projection now threads file-level user-value types, enums,
      structs, and source `using` declarations through raw source-core
      elaboration, and direct `SourceUnit` construction no longer pre-erases
      source types before deployment. The frontend-frontier harness includes a
      constructor-time global UDVT operator `using` witness paired with Forge.
- [x] Pin global user-defined value type operator `using` directives across
      the full overloadable operator family. The solc-AST importer now uses the
      referenced function arity to distinguish unary `-` from binary `-` in
      `using { f as - }`, and the frontend-frontier case executes arithmetic,
      bitwise, comparison, unary negation, and bit-not overloads through Forge
      and imported Lean.
- [x] Pair transient storage call-boundary behavior against solc/Forge:
      ordinary message calls preserve transient writes during the same
      transaction, while the source transaction entry clears transient storage
      before and after execution. The frontend-frontier fixture now checks both
      same-call readback and top-level clearing through Forge and imported
      Lean.
- [x] Strengthen source-core internal-call expression elaboration so binary
      expressions preserve Solidity/Yul-compatible left-to-right source
      sequencing when the left operand is itself a type-conversion, unary, or
      ternary wrapper around a single-return internal/free-function call and
      the right operand is another single-return internal/free-function call.
      The frontend-frontier constructor witness now combines a UDVT operator
      free-function call with a file-level `using` method call in deployment.
- [x] Add `InternalBinaryExpressionElaborationObservation`, exposing the
      Solidity source operand order, short-circuit possibility, left temporary
      boundary, operand elaboration kinds, and source-core expansion result for
      internal-call binary expressions without introducing Solidity-to-Yul
      lowering.
- [x] Extend the solc-AST importer harness lane to state variables and
      assignment expressions with a shared storage-counter `.sol` case, so
      Forge/solc and the imported Lean source interpreter both check storage
      mutation/readback on the same source contract.
- [x] Extend the solc-AST importer harness lane to Solidity mapping types and
      index access expressions with a shared mapping-index `.sol` case, so
      Forge/solc and the imported Lean source interpreter both check abstract
      mapping writes, reads, default values, public getters, and address keys
      before any future relation to Yul/EVM storage-address calculation.
- [x] Extend the solc-AST importer harness lane to event declarations and
      `emit` statements with a shared event-emitter `.sol` case, so Forge/solc
      and the imported Lean source interpreter both check event topic/data
      behavior before any future relation to Yul/EVM `logN` code.
- [x] Promote dynamic indexed event ABI behavior into the paired corpus:
      indexed `bytes` and `string` topics hash the raw dynamic payloads,
      anonymous dynamic events omit the signature topic, and non-indexed
      dynamic payloads remain ABI-encoded data in the source log abstraction.
- [x] Extend the solc-AST importer harness lane to `if` statements and
      `require` calls with a shared branch/revert `.sol` case, so Forge/solc
      and the imported Lean source interpreter both check branch selection and
      source revert-reason behavior before any future relation to generated Yul
      condition/revert code.
- [x] Extend the solc-AST importer harness lane to local variable
      declarations, `while`, `for`, `break`, and `continue` with a shared
      loop-control `.sol` case, so Forge/solc and the imported Lean source
      interpreter both check structured loop control before any future relation
      to Nethermind Yul loop preservation.
- [x] Extend the solc-AST importer harness lane to named function-call
      arguments with a shared internal-call/named-return `.sol` case, so
      Forge/solc and the imported Lean source interpreter both check internal
      call resolution, named-argument ordering, named-return assignment, and
      default return initialization before any future relation to Yul function
      calls.
- [x] Extend the solc-AST importer harness lane to parenthesized singleton
      tuple expressions and Solidity ternaries with a shared expression-control
      `.sol` case, so Forge/solc and the imported Lean source interpreter both
      check short-circuit side effects and selected ternary branch effects
      before any future relation to Nethermind Yul expression evaluation.
- [x] Extend the solc-AST importer harness lane to `UnaryOperation` and inline
      array-literal forms with a shared expression-primitives `.sol` case, so
      Forge/solc and the imported Lean source interpreter both check
      pre/post-increment and decrement, `delete`, logical/bit/negative unary
      operations, type conversions inside unary expressions, and fixed memory
      array literal indexing as source syntax.
- [x] Extend the solc-AST importer harness lane to `IndexRangeAccess` and
      `DoWhileStatement`, and pin receive/fallback function kinds in the
      shared entrypoint-slice-control `.sol` case. Forge/solc checks concrete
      receive/fallback dispatch, calldata bytes/string/array slices and slice
      indexes, calldata-local slice bindings, calldata-slice memory-local
      copies, copy independence under memory-local mutation, and do-while
      results, while the
      imported Lean source interpreter checks the same behavior as abstract
      Solidity source syntax before any future Yul
      dispatcher or loop relation; non-calldata slices, slice members, and
      string index/length member forms are rejected with pinned
      solc/common-checker evidence.
- [x] Extend the solc-AST importer harness lane to `TryStatement` and
      `TryCatchClause`, preserving success return bindings and `Error`,
      `Panic`, raw-bytes, and bare catch clauses in a shared try-catch `.sol`
      case. Forge/solc checks concrete external-call try/catch routing, while
      the imported Lean source interpreter checks the same source behavior
      against explicit abstract external-call oracle and account-code facts
      before any future Yul/EVM failed-call relation.
- [x] Extend the solc-AST importer harness lane to custom error declarations
      and `revert` statements with a shared custom-error `.sol` case, so
      Forge/solc checks real ABI revert bytes while the imported Lean source
      interpreter checks abstract custom error names and argument ordering
      before any future relation to Yul/EVM revert encoding.
- [x] Promote dynamic custom-error ABI payloads into the paired corpus:
      dynamic `string`/`bytes` arguments and tuple-shaped struct arguments now
      check both source `RevertData.custom` payloads and externally observed
      ABI-encoded revert bytes.
- [x] Extend the solc-AST importer harness lane to terminal statement
      outcomes with a shared terminal-statements `.sol` case, so Forge/solc
      checks explicit returns, named-return fallthrough, revert strings,
      custom-error named arguments, and `selfdestruct` halting behavior while
      the imported Lean source interpreter checks abstract source outcomes and
      the checked `TerminalEvaluationObservation`.
- [x] Extend the solc-AST importer harness lane to modifier declarations,
      modifier invocations, and `_` placeholders with a shared modifier-order
      `.sol` case, so Forge/solc and the imported Lean source interpreter both
      check source modifier prefix/body/suffix sequencing and revert rollback
      before any future relation to generated Yul control flow.
- [x] Extend the solc-AST importer harness lane to constructor function
      definitions with a shared constructor-deploy `.sol` case, so Forge/solc
      and the imported Lean source interpreter both check source construction
      entry, state initialization, and constructor revert rollback before any
      future relation to Yul/EVM deployment code.
- [x] Extend the solc-AST importer harness lane to same-file multi-contract
      source units and contract-creation `new` expressions with a shared
      contract-creation `.sol` case, so Forge/solc can inspect the concrete
      child deployment while the imported Lean source interpreter checks the
      abstract Solidity contract-creation request/result before any future
      relation to Yul/EVM create code.
- [x] Extend the solc-AST importer harness lane to inheritance base
      specifiers and explicit base-constructor invocations with a shared
      inheritance-base `.sol` case, so Forge/solc and the imported Lean source
      interpreter both check base constructor execution, inherited storage, and
      derived constructor body effects before any future relation to generated
      Yul deployment and dispatch code.
- [x] Extend the solc-AST importer harness lane to function-call options
      on contract creation with a shared create-options `.sol` case, so
      Forge/solc checks concrete value-bearing `create2` deployment while
      the imported Lean source interpreter checks abstract `{value, salt}`
      contract-creation options before any future relation to Yul/EVM create
      code.
- [x] Extend the solc-AST importer harness lane to high-level external calls
      with `{gas, value}` options using a shared high-level-call-options `.sol`
      case, so Forge/solc checks concrete EVM call/staticcall behavior while
      the imported Lean source interpreter checks the abstract low-level call
      request kind, calldata, value, gas, and returned bytes before any future
      relation to Nethermind Yul/EVM call sequences.
- [x] Extend the solc-AST importer harness lane to Solidity low-level
      `.call`/`.staticcall` return expressions with a shared
      low-level-call-options `.sol` case, and keep the source-core elaboration
      Solidity-faithful by splitting low-level `(bool, bytes)` return values
      before any future relation to Nethermind Yul/EVM call sequences.
- [x] Extend the solc-AST importer harness lane to Solidity tuple
      returns, destructuring declarations, omitted tuple slots, and tuple
      assignment with a shared tuple-destructure `.sol` case, so Forge/solc
      and the imported Lean source interpreter both check multi-value source
      behavior before any future relation to Nethermind Yul `evalValues` and
      return plumbing.
- [x] Factor `ContextObservation` into declaration, ambient call-environment,
      account-oracle, code-oracle, and external-oracle projections so a future
      Nethermind Yul relation can talk about initial source/world inputs
      without importing Yul shared state or compiler memory layout.
- [x] Add `ContractInterfaceObservation` at the Solidity source boundary,
      separating selector-bearing ABI functions, receive/fallback entrypoints,
      constructors, public getters, events, and errors without lowering to Yul.
- [x] Add `SourceUnitInterfaceObservation` for the resolved whole-program
      source surface: contracts, free functions/constants/events/errors,
      type declarations, and source-level using declarations.
- [x] Add `SourceUnitEntryObservation` for whole-program source entry
      selection, packaging resolved interface surface, selected
      contract/function entry names, fuel, and source behavior without choosing
      any generated Yul dispatcher or bytecode entry layout.
- [x] Extend `SourceUnitEntryObservation` with the full source
      `CallObservation` result so top-level entries preserve final source
      state, effects, return values, and revert data in addition to the older
      simplified behavior projection.
- [x] Audit the actual Nethermind Yul/EVM sharing boundary in
      `/Users/dan/Projects/evm-compiler`: Yul and EVM literally share
      `EvmYul.UInt256`, `EvmYul.SharedState`, `EvmYul.State`,
      `EvmYul.MachineState`, execution environment operations, log/memory
      helpers, and precompile definitions; Solidity currently shares the
      source-safe adapters for words, Keccak, block/tx/account lookups,
      call/create requests, logs, selfdestruct records, and selected
      precompile behavior, while intentionally keeping source storage, memory,
      locals, ABI dispatch, and context observations abstract.
- [x] Add `SharedPrimitiveObservation` and
      `Context.observeSharedPrimitive` as a source-owned request/result facade
      for Nethermind-shared primitive meanings: Keccak, environment reads,
      account/code lookups, selected external hash/ecrecover precompile
      behavior, and abstract low-level call/create oracle results, without
      importing Nethermind `SharedState` into the Solidity runtime.
- [x] Add `LowLevelCallResolutionObservation` and
      `ContractCreationResolutionObservation` so the source layer distinguishes
      host/precompile-oracle results from normalized failed-call/create
      fallbacks, giving a later Yul/EVM call relation an explicit abstraction
      boundary without modeling reentrant EVM execution here.
- [x] Add `StateEffectsObservation` and `State.observeEffects` so final
      source logs, selfdestruct records, and external call/create interactions
      are grouped as a relation-ready Solidity effects projection, while
      preserving legacy state-observation fields and keeping storage, memory,
      locals, and ABI dispatch source-owned.
- [x] Add `EventEmissionObservation` so Solidity event emission exposes the
      source event, ABI topics/data, target-shaped log entry, output runtime,
      and source encoding failures before any future relation to Nethermind
      Yul/EVM `logN` builtins.
- [x] Add `RevertPayloadObservation` so Solidity empty/string/dynamic-string
      and custom-error reverts expose argument evaluation effects, source
      `RevertData`, and final reverted source result before any future relation
      to Nethermind Yul/EVM `revert` bytes.
- [x] Add `RequireCheckObservation` so Solidity `assert`/`require` expose
      condition effects, eager dynamic/custom reason evaluation, selected
      source revert payload, and final normal/reverted source result before any
      future relation to generated Yul condition/revert code.
- [x] Add `TryCatchMatchObservation` so Solidity catch-clause selection exposes
      raw external revert bytes, selected `Error`/`Panic`/low-level catch kind,
      decoded source bindings, and unmatched fallback before any future relation
      to Nethermind Yul/EVM failed-call handling.
- [x] Add `ModifierApplicationObservation` so Solidity modifier expansion exposes
      selected modifiers, ordered argument bindings, source placeholder
      replacement, and the resulting core source statement before any future
      relation to generated Yul control flow.
- [x] Add `InternalCallObservation` so Solidity internal/free function calls
      expose overload selection, ordered source arguments, generated
      parameter/return bindings, return storage-ref flags, and source core call
      blocks before any future relation to generated Yul function calls.
- [x] Add internal function-pointer rewrite observations so Solidity
      function-typed local aliases expose source alias resolution, deleted/
      uninitialized panic rewriting, and resolved source call targets before
      any future relation to generated Yul labels or function tables.
- [x] Add `InheritanceDispatchObservation` and dispatch-call rewrite observations
      so Solidity inheritance exposes C3 dispatch order, generated `super`/base
      helper names, and `super.f()`/`Base.f()` source rewrites before any future
      relation to generated Yul function tables or dispatchers.
- [x] Add `UsingExpansionObservation` so Solidity `using` declarations expose
      source method/operator rewriting into library helpers, external-library
      calls, and free-function calls before any future relation to Nethermind
      Yul helper functions or operator lowering.
- [x] Add constant/immutable source observations so Solidity constant inlining,
      source/file-level constant environments, storage/transient/constant/
      immutable declaration classes, and immutable source tags are explicit
      before any future relation to generated Yul constants or immutable
      access code.
- [x] Add expression-control observations so Solidity short-circuit `&&`/`||`
      and ternary condition/branch selection expose skipped versus evaluated
      source subexpressions before any future relation to generated Yul control
      flow.
- [x] Add `HighLevelExternalCallObservation` so Solidity high-level external
      calls expose selector/calldata construction, named-argument ordering,
      `call`/`staticcall`/`delegatecall` choice, value/gas option policy,
      no-return code checks, and return bindings before any future relation to
      Nethermind Yul/EVM call sequences.
- [x] Add `ExternalFunctionValueCallObservation` so external function-typed
      value calls expose address-plus-selector use, ABI argument construction,
      mutability-driven call kind/options, no-return code checks, and return
      bindings before any future relation to Nethermind Yul/EVM call sequences.
- [x] Add `ContractCreationExpressionObservation` so Solidity `new`
      expressions expose constructor ABI argument ordering, value/salt options,
      and source-core contract creation shape before any future relation to
      Nethermind Yul/EVM create sequences.
- [x] Keep this source-refactor phase guarded by checked source examples and
      paired Forge/solc importer cases, so the Solidity semantics remains
      Solidity-faithful while becoming easier to relate to Nethermind Yul
      later.

## Solidity Source Semantics

- [x] Keep `L00_SourceSolidity/Interface.lean` as the canonical source surface.
- [x] Move source typechecking out of the compiler pass namespace.
- [x] Remove the local compiler-pipeline attempt from this branch.
- [x] Add Nethermind `EVMYulLean` as a pinned reference submodule under
      `external/nethermind/EVMYulLean`.
- [x] Add an `EvmYul.UInt256` compatibility surface for the Nethermind word
      primitive API used by the source semantics.
- [x] Route word-level Solidity wrappers through the shared `EvmYul.UInt256`
      adapter.
- [x] Route Solidity Keccak/selector helpers through an `EvmYul.SpongeHash`
      compatibility primitive surface.
- [x] Route block/transaction environment reads and `blockhash`/`blobhash`
      through shared block semantics.
- [x] Route account, log, low-level call, and contract-creation wrappers through
      named shared adapters.
- [x] Replace remaining generic hash/ecrecover maps with address-keyed shared
      precompile calls where useful.
- [x] Route Solidity call gas options and `send`/`transfer` stipends through
      gas-aware shared low-level call requests.
- [x] Model external function pointer ABI values as address-plus-selector
      runtime values, including `.address`, `.selector`, and
      `abi.encodeCall` over external function-typed variables.
- [x] Execute calls through external function-typed values via the stored
      address and selector, including return decoding, `{gas, value}` options,
      and `try/catch` routing.
- [x] Preserve recursive source ABI canonicality through ordinary dispatch,
      generated public getters, inheritance-aware constructor calldata,
      `abi.decode`, and high-level external return decoding; high-level calls
      decode against the callee's declared return types before destination
      conversions.
- [x] Pin source-owned dynamic `bytes`/`string` reference behavior across
      memory aliases, calldata-to-memory copies, storage aliases and copies,
      nested struct members, short/long storage transitions, push/pop, empty
      pop panic, and storage-array push assignment without exposing EVM storage
      layout.
- [x] Route public/external Solidity library calls through context-provided
      library addresses and shared `delegatecall` low-level call requests.
- [x] Deepen the named adapters with direct shared state/log/call/precompile
      semantics where the Solidity source layer has a matching primitive,
      while leaving closed-world host behavior as explicit oracle records.
- [x] Finish source typechecking coverage for Solidity 0.8.35 features under
      the approved source-layer boundaries below.
- [x] Enforce calldata-origin aliasing through local declarations,
      reassignment, internal function/modifier/library arguments, returns, and
      tuple/multi-return propagation, while treating external contract calls
      and public/external non-storage library parameters as ABI copy
      boundaries.
- [x] Finish executable source semantics for try/catch, libraries, payable,
      inheritance dispatch, modifiers, rollback, events, errors, and data
      locations.
- [x] Add small executable source examples for each supported Solidity feature.
- [x] Record unsupported Solidity behavior and final source-layer boundaries
      explicitly.

## Active Solidity Semantics Completion

- [x] Establish an 83-case pinned-solc/Forge/imported-Lean baseline with
      fail-closed whole-AST coverage and explicit invalid-source lanes.
- [x] Enforce calldata-origin rules across aliases, calls, returns,
      reassignment, tuples, modifiers, and library ABI boundaries.
- [x] Sequence source result conversions around abstract high-level external
      calls and external function-value calls, including direct and `using`
      public-library delegatecalls with dynamic reference arguments.
- [x] Match reference-delete location and alias semantics: reject deletion of
      calldata references and storage pointers; rebind deleted memory arrays,
      fixed arrays, structs, bytes, and strings to fresh defaults without
      mutating existing aliases; mutate shared objects for nested deletes.
- [x] Pin storage mapping reference semantics against solc: local mapping
      aliases, nested mapping aliases, and mapping members inside storage
      structs execute through abstract storage paths; local storage-reference
      rebinding preserves Solidity aliasing; deleting a struct containing a
      mapping resets scalar fields while preserving mapping entries; direct
      mapping deletes, memory mapping values, storage copies of structs
      containing mappings, and non-storage placements of those structs are
      rejected.
- [x] Preserve parameter and return data locations in function types: compare
      memory/calldata/storage locations for internal function values and calls,
      retain explicit external pointer-type locations, and canonicalize values
      obtained from external declarations to ABI-boundary memory locations.
- [x] Pin function-typed expression named-call acceptedness against solc:
      calls through function-typed values reject named arguments even when the
      function type spells deprecated parameter names.
- [x] Pin function-type ABI exposure acceptedness against solc: public/external
      ABI boundaries reject external function types containing internal
      functions or storage mappings, internal payable function types, internal
      function pointer parameters, invalid `public` function-type visibility,
      public internal-function state getters, and public getters for structs
      containing internal functions, while external function pointer parameters,
      payable external function types, and public external-function pointer
      getters remain accepted.
- [x] Match solc definite assignment for named storage/calldata pointer returns
      across branches, terminal paths, loops, explicit reads/returns, and
      modifier placeholder continuations; execute direct calldata bindings and
      storage-pointer returns through modifiers in the checked interpreter.
- [x] Preserve exact parameter/return data locations when overriding
      non-external functions and modifiers, while retaining solc's canonical
      external-boundary rule that allows memory/calldata spelling changes;
      distinguish pure-compatible bare storage pointers from state-reading
      storage projections.
- [x] Match inherited callable identity across unrelated and dominated base
      declarations: require overrides for unrelated abstract/concrete members,
      retain descendant dominance for abstract functions and modifiers, reject
      bodyless overrides of implemented members, and keep data locations out of
      overload signature identity.
- [x] Match address/contract explicit-conversion payability: nonpayable
      addresses cannot convert to contracts with direct or inherited payable
      receive/fallback entrypoints, payable addresses can, and payable contract
      conversion recognizes inherited Ether-receiving behavior.
- [x] Match one-step address value conversions: nonpayable addresses convert
      directly to and from `bytes20` and `uint160`, while payable addresses
      require an explicit intermediate `address` conversion and wrong-width
      fixed-bytes/integer targets remain rejected.
- [x] Pair Solidity's fixed/ufixed declaration-only boundary against solc:
      private declarations, mappings, ABI canonical spelling, user-value-type
      underlyings, and unused locals are accepted; invalid shapes, executable
      fixed-point reads/returns/assignments/initializers, public getters,
      implicit fixed conversions, and fixed-point operators are rejected.
- [x] Separate transient library type expressions from value-bearing type
      positions: preserve `address(L(x))` and `type(L)` while rejecting library
      types in declarations, ABI values, mappings, arrays, function types, and
      `using for` targets.
- [x] Make `type(T).creationCode` and `.runtimeCode` kind-sensitive: accept
      concrete contracts and libraries, reject interfaces and abstract
      contracts, and execute `bytes(type(T).name)` at the abstract source layer.
- [x] Restrict `.balance`, `.code`, and `.codehash` to actual address values;
      contract and transient library values require Solidity's explicit
      `address(...)` conversion before account-environment member access.
- [x] Distinguish type-namespace and bound function members: preserve
      contract/interface/library namespace selectors and bound
      contract/interface `.selector`/`.address`, reject transient-library
      members and namespace `.address`, exclude library functions from
      `abi.encodeCall`, and execute scalar one-argument `encodeCall` ASTs.
- [x] Match solc definite assignment for uninitialized local storage/calldata
      pointers across unused declarations, straight-line and both-branch
      assignment, do-while, maybe-executed loops, and lexical shadowing; treat
      local storage-pointer rebinding as a read-only alias operation and execute
      first assignment through an unobservable source alias sentinel.
- [x] Execute runtime inheritance-list base-constructor arguments in the source
      layer: accept environment reads, file-scope free calls, file- and
      contract-scope `using`, external/self calls through the abstract external
      protocol, constructor parameters, `msg.value`, and abstract balances while
      preserving solc's state/current-function/header type rejections.
- [x] Preserve nominal Solidity struct identity at the source typechecker while
      using tuple-shaped abstract ABI payloads for structs: short local names
      alias their current contract-qualified type only, and `abi.encode` /
      `abi.decode` round-trip a dynamic-field struct without exposing compiler
      memory layout.
- [x] Pair ABI coder mode selection against solc: preserve real
      `pragma abicoder v1` through AST import, accept dynamic arrays of static
      elements, reject structs and nested dynamic arrays as v2-only at ABI
      boundaries, and reject duplicate coder pragmas.
- [x] Pair source-unit pragma directive acceptedness against solc: version
      ranges, unknown pragmas, unsupported experimental features, duplicate
      experimental declarations, bad `abicoder` values, and the order-sensitive
      `pragma abicoder v2; pragma experimental ABIEncoderV2;` legacy boundary
      agree between pinned solc and the common checker.
- [x] Expose the explicit source-layer exclusion boundary in the harness:
      unresolved imports and inline assembly/Yul remain checked-source
      rejections by user-approved scope, even though raw execution and solc
      parsing are separate concerns.
- [x] Pair ABI encoding helpers against solc: `abi.encodePacked` for scalar,
      dynamic-array, and external-function values, selector/signature encoding
      including runtime signatures, selector/signature first-argument
      acceptedness, and packed-mode struct/nested-array rejection.
- [x] Pair Solidity concat builtins against solc: `bytes.concat` with fixed
      bytes, dynamic bytes, and hex literals, plus `string.concat` with
      ordinary and unicode string inputs, execute through the abstract source
      byte/string value model without exposing compiler memory layout; pinned
      solc and the common checker reject non-bytes `bytes.concat` arguments
      and non-string `string.concat` arguments.
- [x] Pair malformed `bool` ABI canonicality against solc: external dispatch,
      `abi.decode`, and high-level external return decoding reject non-`0/1`
      ABI words with empty-data reverts while preserving the existing dynamic
      padding permissiveness.
- [x] Pair top-level scalar ABI cleanup eagerness against solc: malformed
      external `bool`, `address`, fixed-bytes, enum, signed narrow integer, and
      unsigned narrow integer parameters reject before body execution even when
      the parameter is unnamed and unused.
- [x] Pair fixed-size array ABI narrow-element cleanup against solc:
      malformed accessed `uint8[2]` calldata rejects when the element is
      observed, a dirty unaccessed fixed-array element remains accepted through
      external calldata dispatch, and malformed fixed-array elements reject
      when `abi.decode` or high-level external return decoding materializes the
      whole array.
- [x] Pair nested calldata aggregate ABI cleanup laziness against solc:
      malformed dynamic-array elements do not poison `.length`, and malformed
      struct/tuple fields do not poison sibling field reads, while observing
      the dirty element or field still reverts with empty data.
- [x] Pair constructor ABI strict aggregate cleanup against solc: malformed
      narrow elements inside constructor dynamic arrays, fixed arrays, and
      structs reject deployment before source constructor execution, even when
      the constructor body reads only aggregate length or a clean sibling.
- [x] Pair event/error shadowing and named-argument ABI behavior against solc:
      free declarations, contract-local shadowing, inherited declarations,
      named event arguments, custom-error selectors, and event topics/data
      agree between Forge, solc AST import, and the checked source interpreter.
- [x] Pair callable override signature/base-list acceptedness against solc:
      reject return-type, visibility, mutability, missing multi-base override
      list, and incomplete explicit base-list mismatches in the common checker.
- [x] Pair callable overload signature identity against solc: reject overloads
      that differ only by data location, return type, parameter name,
      visibility, or mutability, while preserving ordinary parameter-type
      overloads.
- [x] Pair declaration signature identity against solc: modifiers and custom
      errors are name-unique, events may overload by ABI parameter types, and
      duplicate event ABI signatures ignore parameter names and `indexed`
      markers.
- [x] Pair inherited declaration/name shadowing acceptedness against solc:
      visible inherited state variables, functions, user types, modifiers,
      events, and errors reject local declaration collisions in the common
      checker, private inherited names remain shadowable where Solidity allows,
      and representative pinned-solc invalid lanes cover state-variable,
      function-vs-state, function-vs-type, and inherited-event duplicate
      collisions.
- [x] Execute private inherited state-variable shadowing with origin-sensitive
      abstract storage identity: base and derived private same-name fields get
      distinct source-level runtime keys, while lexical function bodies,
      inherited internal calls, public getter bodies, aliases, state
      initializers, and constructors still use ordinary Solidity names at the
      source boundary.
- [x] Pair event static acceptedness against solc: mapping and internal
      function event parameters reject, non-anonymous events allow at most
      three indexed parameters while anonymous events allow four, anonymous
      event `.selector` access rejects, and unknown emitted events reject.
- [x] Pair custom-error static acceptedness against solc: reserved
      `Error`/`Panic` names, duplicate parameter names, overloading, unknown
      custom-error reverts, data-location annotations, and local-error
      shadowing with the wrong argument shape reject, while named custom-error
      arguments and file/contract shadowing with matching local shapes execute.
- [x] Pair try/catch static acceptedness against solc: only external function
      calls and known contract creation are valid try targets, try return
      bindings must match returned values and use memory for reference types,
      catch Error/Panic/bytes headers must have Solidity's exact shapes,
      duplicate catch kinds reject, and try statements require at least one
      catch clause.
- [x] Pair declaration data-location acceptedness against solc:
      reference-typed function parameters and returns require explicit data
      locations where Solidity requires them, value-typed parameters reject
      data-location annotations, externally visible contract functions reject
      storage parameters and storage returns, constructors match solc's
      deployable versus abstract/internal storage-parameter boundary, modifiers accept
      storage/memory/calldata reference parameters while rejecting missing or
      value-typed locations, custom-error parameters reject data-location
      annotations in the common checker, and event/error source spelling with
      data locations is pinned as solc rejection.
- [x] Pair fallback/receive callable-form acceptedness against solc:
      interfaces may declare unimplemented fallback/receive entries, typed
      fallback is restricted to `bytes calldata -> bytes memory`, receive is
      external payable with no params or returns, duplicate fallback/receive
      entries reject, and libraries reject fallback/receive declarations.
- [x] Pair receive/fallback ABI dispatch against solc: empty calldata selects
      `receive` when present or `fallback` otherwise, unknown calldata selects
      `fallback`, typed fallback returns raw calldata as returndata, matching
      function selectors take precedence, missing receive/fallback entries
      reject with empty returndata, and inherited/overridden entries dispatch
      through Solidity's source-level override rules.
- [x] Pair ABI selector-collision acceptedness against solc: external
      functions and generated public getters with distinct canonical ABI
      signatures but the same 4-byte selector reject in the common checker,
      including direct declarations and inherited dispatch surfaces, matching
      solc's function-signature-hash-collision behavior while caching selector
      words before duplicate detection so real-project imports remain within
      Lean heartbeat limits.
- [x] Pair deprecated constructor-visibility acceptedness against solc:
      concrete `public` and abstract `internal` constructors are accepted with
      warnings, while concrete `internal`, abstract `public`, `private`, and
      `external` constructors reject.
- [x] Pair callable header and fallback/receive override acceptedness against
      solc: fallback/receive overrides require/accept `override` with matching
      mutability, constructors and free functions reject invalid `virtual` and
      `payable` specifiers, and bodyless fallback declarations require
      `virtual`.
- [x] Pair call-option placement and typing acceptedness against solc:
      contract creation accepts `value`/`salt` only with `bytes32` salts,
      high-level external calls accept `gas`/`value` only with unsigned
      amounts, call options on super/internal/array-member calls reject,
      low-level calls restrict options by member kind and reject named
      arguments, and duplicate options reject.
- [x] Pair numeric and fixed-bytes one-step conversion acceptedness against
      solc: execute width/sign-preserving integer conversions, fixed-bytes
      widening/narrowing, and same-width fixed-bytes/integer conversions, while
      rejecting casts that change both width and sign or both width and
      representation category.
- [x] Pair nested memory reference aliasing against solc: dynamic arrays nested
      in memory and struct dynamic-array fields alias through whole-value
      assignment and path selection at the abstract Solidity source layer,
      without introducing EVM byte-addressed memory layout.
- [x] Pair calldata-to-memory deep-copy behavior against solc: dynamic arrays
      of structs with nested dynamic `bytes` fields copy into independent
      memory objects, so mutations to nested bytes and scalar fields in the
      memory copy leave the calldata source unchanged.
- [x] Pair storage-to-memory deep-copy behavior against solc: dynamic storage
      arrays of structs with nested dynamic `bytes` fields copy into
      independent memory objects, so mutations to the memory copy leave the
      storage source unchanged.
- [x] Pair storage-to-storage deep-copy behavior against solc: dynamic storage
      arrays of structs with nested dynamic `bytes` fields copy into
      independent storage destinations, so mutations to the destination array
      leave the source array unchanged.
- [x] Pair storage local aliasing for dynamic arrays of structs with nested
      dynamic `bytes`: mutating nested bytes and scalar fields through a
      storage local reference mutates the original storage array.
- [x] Pair mapping values with dynamic reference contents against solc:
      deleting storage mapping entries whose values are dynamic arrays,
      `bytes`, `string`, or structs containing dynamic array/`bytes` fields
      restores source-visible defaults for the selected key without disturbing
      neighboring keys.
- [x] Pair via-IR memory-to-storage deep-copy behavior against solc: dynamic
      memory arrays of structs with nested dynamic `bytes` fields materialize
      recursively at the abstract storage-write boundary, so later mutations to
      the memory source leave the storage destination unchanged without
      modeling byte-addressed compiler memory layout.
- [x] Pair free-function reference boundaries against solc: memory and
      calldata reference parameters/returns preserve Solidity-visible source
      values at their declared locations, and storage reference returns remain
      aliases that mutate the original abstract storage object.
- [x] Pair memory allocation expressions against solc: `new T[](n)`,
      `new bytes(n)`, and `new string(n)` allocate abstract memory values with
      Solidity-visible default contents and lengths; nested dynamic arrays keep
      default element semantics, while fixed-array allocation, invalid arities,
      and signed lengths reject statically.
- [x] Pair array literal acceptedness against solc: execute fixed-size inline
      array literals, reject empty array literals, and reject array literals
      whose elements have no common Solidity element type.
- [x] Pair tuple-hole acceptedness against solc: omitted tuple components are
      accepted in declaration/assignment binding positions but rejected in
      value positions such as returns, declaration initializers, and
      assignment right-hand sides; tuple declarations without required
      initializers, tuple type/arity mismatches, and non-lvalue assignment
      targets reject.
- [x] Pair tuple-index acceptedness against solc: tuple destructuring remains
      source-supported, but indexing tuple expressions or multi-return call
      results is rejected at the Solidity source boundary.
- [x] Pair local binding scope acceptedness against solc: duplicate locals in
      the same block reject, while nested block shadowing is accepted and
      executes at the abstract source layer.
- [x] Pair loop-control placement against solc: `break` and `continue`
      execute inside while/for loops and reject outside loops.
- [x] Pair unchecked-block placement against solc: ordinary unchecked
      arithmetic is accepted, while nested unchecked blocks and modifier
      placeholders inside unchecked blocks reject.
- [x] Pair state-mutability acceptedness against solc: pure/view restrictions
      reject state reads, writes, emits, creates, and calls through direct
      bodies and applied modifiers, while inherited modifier helper calls still
      resolve in the abstract source checker.
- [x] Pair `require`/`revert` builtin acceptedness against solc: accepted
      string/custom-error payload forms stay executable while invalid
      non-string/non-error reason payloads reject.
- [x] Expose every currently named common-checker aggregate witness in the
      Forge/solc/imported-Lean manifest, including constructor data-location,
      modifier data-location, and fixed-point ABI canonicality checks.
- [x] Pair enum ABI strict-cleanup behavior against solc: malformed enum
      calldata, `abi.decode` payloads, and high-level external return data
      reject values outside the declared enum range while source-level enum
      values still convert explicitly to unsigned integers.
- [x] Pair deterministic global primitive builtins against solc:
      `addmod`/`mulmod` use Solidity's arbitrary-precision modular arithmetic
      and panic on zero modulus, `keccak256` hashes bytes-like payloads, and
      signed modular operands plus non-bytes hash payloads reject statically.
- [x] Pair `assert` builtin behavior against solc: boolean assertions return
      normally, false assertions panic with `0x01`, failed assertions roll back
      state writes, and non-bool assert conditions reject statically.
- [x] Pin calldata slice-bound typing against solc: unsigned calldata byte,
      string, and array slice bounds remain accepted, while signed slice bounds
      reject statically.
- [x] Pin calldata slice member-call typing against solc: slice indexing and
      calldata-local slice bindings remain accepted, while direct slice member
      access and `using`-library member calls on slices reject statically.
- [x] Extend calldata-origin acceptedness beyond memory sources: pinned solc
      and the common checker now reject storage-to-calldata local bindings,
      returns, internal calls, reassignment, and tuple destructuring, matching
      the existing memory-to-calldata rejection family.
- [x] Pin low-level call-option name discipline against solc: ordinary
      gas/value low-level calls remain accepted, while duplicate gas/value or
      unknown low-level call options reject statically.
- [x] Pair packed storage scalar/struct/fixed-array behavior against solc:
      narrow top-level fields, narrow struct fields, and packed fixed arrays
      write/read through the abstract source storage model while preserving
      source-visible getter results.
- [x] Pair indexed event topic hashing for arrays and structs against solc:
      indexed dynamic arrays, fixed arrays, static struct/tuple parameters, and
      dynamic arrays whose elements are dynamic `bytes`, plus structs with
      nested dynamic `bytes` members and dynamic arrays of those structs, are
      hashed with Solidity's event-indexed in-place encoding, while source
      event observations still retain the abstract indexed/data values.
- [x] Extend high-level external return-data strictness against solc:
      malformed `address` high bits and dirty `bytes4` padding returned by an
      abstract call now revert with empty data just like the existing bool,
      enum, narrow integer, dynamic bytes, and nested-array return-data
      boundary cases; ignored malformed components in multi-return external
      calls and external function-value calls are still decoded and rejected
      before named return components are assigned.
- [x] Pair public external-function pointer state getter semantics against
      solc: external function values store/load through typed abstract
      storage, generated public getters ABI-encode address-plus-selector
      values, `.address`/`.selector` on stored function values use the stored
      pointer rather than the public getter selector, and calls through stored
      pointers use the abstract low-level call boundary.
- [x] Pair dynamic-array and `bytes` mutator-member acceptedness against solc:
      storage dynamic arrays and storage `bytes` accept `push`/`pop` including
      no-argument push-return references, while memory/calldata/fixed-array/
      string receivers, named `push`, bad `pop` arity, wrong `bytes.push`
      element types, and view-state mutations reject in the common checker.
- [x] Pair `.length` lvalue/update acceptedness against solc: array and
      `bytes` length reads remain ordinary source expressions, but storage,
      memory, and fixed-array `.length` assignment plus increment/decrement
      attempts reject in the common checker.
- [ ] Continue the pinned-solc acceptedness audit beyond calldata origins,
      covering remaining memory/storage/calldata placement, conversion,
      overload, inheritance, and callable-form constraints.
- [ ] Expand differential reference-type coverage for nested arrays, structs,
      mappings, bytes/string, storage references, copies, aliases, mutation,
      and return/argument boundaries until no unclassified source behavior
      remains.
- [ ] Expand differential ABI coverage for selectors, dispatch, malformed
      inputs and returns,
      remaining event/error edge cases, function values, constructors, and
      library boundaries.
- [x] Implement and pair high-level external calls embedded in non-call
      expression contexts such as ternary conditions, preserving Solidity's
      source-level evaluation order and malformed-return empty-data reverts.
- [x] Pin high-level external calls embedded in ternary local-declaration
      initializers and assignment right-hand sides, confirming the existing
      source-level conditional-assignment projection preserves malformed-return
      empty-data reverts outside direct return position.
- [ ] Audit every remaining Solidity 0.8.35 source feature outside imports and
      inline assembly/Yul, close each semantic gap, and record intentional
      abstractions separately from unsupported source behavior.
- [ ] Finish only when the common checker, checked executable semantics,
      fail-closed solc-AST corpus, and focused invalid-program corpus jointly
      support the completeness claim; external-world concretization and any
      Solidity-to-Yul compiler remain separate future goals.

## Boundary Rules

- Parser/frontend success is not source semantics unless separately verified:
  raw parsing, import resolution/remappings, source maps, Standard JSON,
  diagnostics, warnings, metadata, codegen, optimizer, and bytecode output are
  outside this source-layer model.
- The solc-AST frontend should use the whole AST as its fail-closed ingestion
  denominator for the pinned Solidity 0.8.35 corpus: every node kind,
  source-bearing child field, source scalar field, and finite source scalar
  value that appears must be classified and either rendered into the abstract
  Solidity source layer, recorded as metadata/analysis, or rejected as
  explicitly out of scope. This does not mean every solc JSON field is part of
  the source semantics.
- Inline assembly/Yul and unresolved imports are explicitly out of scope for the
  Solidity source semantics.
- Compiler convenience must not shape Solidity semantics.
- External contracts, host behavior, closed-world gas/resource consumption,
  account nonce/address allocation, reentrant execution, and heavy precompile
  execution may remain explicit `External`/context oracle records at the
  Solidity layer.
- Shared primitive behavior should be imported through named modules when
  Solidity is simply exposing Yul/EVM behavior.
- Solidity storage and memory remain source-owned abstractions because they
  carry source data-location, reference, aliasing, and type behavior; solc's
  byte-addressed compiler memory layout is intentionally not modeled here.
- Solidity's unspecified sibling expression order is modeled by the
  Yul-compatible deterministic child policy.
- `fixed`/`ufixed` are modeled at solc's declaration-only boundary: accepted
  where solc accepts static declarations, rejected for executable values,
  public getters, assignments, returns, and ABI/runtime use.
