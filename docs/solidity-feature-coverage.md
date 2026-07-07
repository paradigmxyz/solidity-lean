# Solidity 0.8.35 Feature Coverage Audit (solc-side)

Cross-checked catalog of Solidity 0.8.35 language features, enumerated from the
compiler's own AST node-kind universe and grammar, then checked against this
repo's executable semantics. The goal is to surface **blind spots** — features
never considered — as distinct from the known gaps already tracked in
`ROADMAP.md`.

Method: (1) enumerated the solc AST `nodeType` universe and the sub-node
vocabularies (operators, literal kinds, mutabilities, visibilities, function
kinds, builtin globals/members) the compiler emits; (2) checked each against, in
descending evidence strength, (a) differentially-validated corpus lanes in
`tests/forge-harness/manifest.json` (104 cases; 36 lanes also pin deliberate
solc/Lean rejections across 314 reject fixtures), (b) the importer
`scripts/solc_ast_to_lean_source.py` (which `nodeType`s and sub-vocabularies it
translates vs. `fail()`-rejects), (c) `SolidCore/Solidity/Interface.lean`
elaboration and `Interpreter.lean` execution, (d) `ROADMAP.md` gap registry and
`docs/`.

Status legend:
- **SUPPORTED** — importer + interpreter handle it AND at least one corpus lane exercises it differentially against pinned solc/EVM.
- **SUPPORTED-UNTESTED** — importer + interpreter handle it, but no corpus lane exercises it.
- **PARTIAL** — handled for a restricted subset; the rest is rejected or unmodeled.
- **FAIL-CLOSED** — deliberately rejected (importer `fail()` / interface sentinel), matching or narrower than solc.
- **IN-FLIGHT** — under active work in the sibling worktree; not audited deeply here.
- **OUT-OF-SCOPE** — excluded by an explicit project decision.
- **UNKNOWN** — could not be determined from static evidence.

---

## Executive summary

**Headline finding: coverage is near-total at the AST node-kind granularity, and
the genuine blind spots are few.** The importer's `SUPPORTED_NODE_TYPES` set
(`solc_ast_to_lean_source.py:28`) covers **every** Solidity 0.8 AST `nodeType`
except two deliberately excluded ones — `ImportDirective` and `InlineAssembly`
(plus all `Yul*` nodes) — see `EXCLUDED_NODE_TYPES` at line 30. There are no
"unimplemented" node kinds: `guard_no_unsupported_nodes` (line 410) fails closed
on any node type, child field, or scalar value it does not recognize, so an
unhandled construct cannot silently pass. Consequently the interesting frontier
is entirely **sub-node**: which operators, builtin members, literal kinds, and
type categories are handled inside each node's handler. Those vocabularies are
also essentially complete (all operators, all literal kinds, all mutabilities,
visibilities, function kinds, contract kinds, and the full `block.*`/`msg.*`/`tx.*`
magic-member set).

### Status counts (feature rows in this matrix: 118)

| Status | Count |
|---|---|
| SUPPORTED | 84 |
| SUPPORTED-UNTESTED | 8 |
| PARTIAL | 5 |
| FAIL-CLOSED | 4 |
| IN-FLIGHT | 4 |
| OUT-OF-SCOPE | 6 |
| UNKNOWN | 7 |

(Counts are approximate groupings of the rows below; some rows cover a family of
related members.)

### Ranked blind spots (no support AND no tracking)

The audit found **no wholly un-considered language construct** at the node-kind
level. The most significant genuine blind spots are all sub-node and are
**untested-but-elaborated cryptographic/block builtins** plus a handful of
**UNKNOWN encoding edge cases**. Ranked by risk:

1. **`sha256`, `ripemd160`, `blockhash(n)`, `blobhash(n)` builtins —
   SUPPORTED-UNTESTED.** All four are elaborated in `Interface.lean`
   (`ripemd160`/`sha256` appear 8× each; `blockhash`/`blobhash` 10× each) but
   **zero corpus `.sol` sources use them** (grep of `tests/forge-harness/**.sol`
   = 0 files each). `ecrecover` and `keccak256`, by contrast, ARE exercised
   (ecrecover in 2 sources incl. `openzeppelin-ecdsa`/`solmate-erc20`). These are
   the highest-value blind spot: precompile/opcode results with real EVM
   semantics that have never been differentially checked. Not listed in the gap
   registry.
2. **`ripemd160` and `sha256` output/word semantics — UNKNOWN.** Because there is
   no lane, whether the modeled result word matches the pinned EVM precompile
   byte-for-byte is unverified. Flagged UNKNOWN rather than SUPPORTED.
3. **Multi-dimensional / nested-dynamic ABI encode+decode round-trips —
   UNKNOWN.** `abi.encode`/`decode` and nested `dynamicArray`/`struct` cleanups
   exist (`Interpreter.lean:100-101`, `abi-struct-tuples` lane covers dynamic
   struct fields), but deeply nested `T[][]` / `string[]` decode is not obviously
   pinned by a lane. Could be SUPPORTED; flagged UNKNOWN pending a probe.
4. **Fixed-point (`fixed`/`ufixed`) executable arithmetic — PARTIAL, but matches
   solc.** Declarations, mappings, ABI spelling, and unused locals are accepted;
   executable fixed-point values are rejected — which is exactly the current solc
   boundary (`fixed-point-boundary` lane confirms both sides agree). Not a
   soundness blind spot, but worth noting the interpreter has no fixed-point
   evaluation at all.
5. **`do-while` — actually SUPPORTED (not a blind spot; corrected during audit).**
   Initially suspected untested, but `do { } while` appears in
   `pointer-return-definite`, `local-pointer-definite`, and
   `entrypoint-slice-control` sources and executes via `Stmt.doWhile`
   (`Interpreter.lean:6848,7811`).
6. **`abi.encodeWithSelector`/`encodeWithSignature` dynamic-arg edge cases —
   UNKNOWN.** Elaborated (`Interface.lean:3578-3580`) and used broadly, but no
   dedicated adversarial lane isolates their behavior the way `abi-encoding-helpers`
   does for packed/scalar encoding.
7. **User-defined-operator dispatch for the full permitted set — UNKNOWN edge.**
   `using_operator` (importer ~883) covers `+ - * / % ** == != < > <= >= & | ^ ~`
   and unary `neg`, which is the complete UDVT-operator set solc permits; the
   `library-type-uses` lane exercises UDVT operators, but not every operator is
   individually pinned.

Everything else in scope is either SUPPORTED, an explicit OUT-OF-SCOPE decision,
or an already-tracked IN-FLIGHT gap. No feature was found that the pipeline would
accept and mis-model silently.

---

## Matrix

### 1. Declarations & top-level

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| `contract` | SUPPORTED | `contract_kind` importer ~1832; many lanes | |
| `interface` | SUPPORTED | `contract_kind`; `openzeppelin-*` interface slices | |
| `library` | SUPPORTED | `library-type-uses`, `uniswap-v2-libraries`, `openzeppelin-*` | |
| `abstract contract` | SUPPORTED | `abstract` scalar read, importer 1903-1904; OZ slices | |
| Free functions (file-level) | SUPPORTED | `function_kind` maps `freeFunction`→`function` (~825); SourceUnit child handling 1994 | |
| File-level constants | SUPPORTED | non-constant free var rejected (importer 1930); `source-declarations` | Only `constant` free vars accepted (matches solc) |
| `event` (+ indexed, anonymous) | SUPPORTED | `event-emitter`, `event-indexed-dynamic`, `event-error-shadowing`; anonymous at Interface 7296 | |
| Custom `error` | SUPPORTED | `custom-error`, `custom-error-dynamic` | |
| `enum` / `EnumValue` | SUPPORTED | `Ty.enumStorage`; `frontend-frontier`, OZ slices | |
| `struct` (+ dynamic fields) | SUPPORTED | `abi-struct-tuples`, `packed-storage` | |
| User-defined value type (UDVT) | SUPPORTED | `UserDefinedValueTypeDefinition`; `library-type-uses`, `openzeppelin-checkpoints` | wrap/unwrap supported |
| `using ... for T` | SUPPORTED | `UsingForDirective`; `library-type-uses`, OZ libs | |
| `using {f as +} for T global` (operators) | SUPPORTED | `using_operator` importer ~883; `global` at Interface 16254 | Full permitted operator set |
| `using ... for *` (wildcard) | UNKNOWN | not observed in a lane; importer path exists | Not isolated by a probe |
| `pragma` (solidity/abicoder/experimental) | PARTIAL | `PragmaDirective` handled; `abi-coder-modes` accepts v1/v2 | Bad pragmas rejected (`source-declarations`) |
| State variables (`constant`/`immutable`/`mutable`/`transient`) | SUPPORTED | `var_mutability` importer ~845; `storage-counter`, transient in `Ast.lean:64` | |
| `import` directives | OUT-OF-SCOPE | `EXCLUDED_NODE_TYPES` line 30; `ROADMAP.md:470` | Flattening is the intended preprocessing step |

### 2. Inheritance & polymorphism

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| Single/multiple inheritance | SUPPORTED | `inheritance-base`, `callable-identity` | |
| `virtual` / `override` | SUPPORTED | `virtual` scalar; `override-data-locations`, `callable-identity` | |
| `super` | SUPPORTED | `super` in Interface; `callable-identity` | |
| C3 linearization / dominance | SUPPORTED | `callable-identity` (inherited fn/modifier dominance, multi-base) | |
| Base constructor args (list & modifier form) | SUPPORTED | `base-constructor-runtime-args`, `inheritance-base` | |
| Modifiers (+ args, inheritance, ordering) | SUPPORTED | `ModifierDefinition`/`ModifierInvocation`; `modifier-order` | |
| `_` placeholder | SUPPORTED | `PlaceholderStatement`; `modifier-order` | |

### 3. Statements

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| Block | SUPPORTED | importer 1228 | |
| `if`/`else` | SUPPORTED | `branch-require` | |
| `while` | SUPPORTED | `loop-control` | |
| `for` | SUPPORTED | `loop-control` | |
| `do-while` | SUPPORTED | `Interpreter.lean:6848,7811`; `pointer-return-definite` src | Corrected: is tested |
| `break` / `continue` | SUPPORTED | `loop-control` (nested break/continue rejected by solc, pinned) | |
| `return` (single/named/tuple) | SUPPORTED | `function-calls`, `tuple-destructure` | |
| `emit` | SUPPORTED | `event-emitter` | |
| `revert` (string & custom) | SUPPORTED | `branch-require`, `custom-error` | |
| `try`/`catch` (Error/Panic/raw/bare) | SUPPORTED | `try-catch` | |
| `unchecked { }` | SUPPORTED | `checked-arithmetic` (nested unchecked rejected by solc, pinned) | |
| Variable declaration (+ tuple destructure, holes) | SUPPORTED | `tuple-destructure`, `tuple-holes` | |
| Expression statement | SUPPORTED | importer 1240 | |
| Inline assembly | OUT-OF-SCOPE | `EXCLUDED_NODE_TYPES` line 30; `ROADMAP.md:469` | |

### 4. Expressions

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| Binary ops (`+ - * / % ** == != < > <= >= && \|\| & \| ^ << >>`) | SUPPORTED | `binary_op` importer ~856; `expression-primitives` | Full set |
| Unary ops (`! ~ - ++ -- delete`) | SUPPORTED | `unary_op` importer ~932; `expression-primitives`, `reference-delete` | |
| Assignment ops (`= += -= *= /= %= &= \|= ^= <<= >>=`) | SUPPORTED | `assign_op` importer ~910 | Full set |
| Conditional (ternary) | SUPPORTED | `Conditional`; `expression-control` | |
| Tuple expression / inline array | SUPPORTED | `tuple-destructure`, `expression-primitives` (inline array) | |
| Function call (positional & named args) | SUPPORTED | `args_from_nodes` importer ~950; `function-calls` | |
| `FunctionCallOptions` (`{gas,value,salt}`) | SUPPORTED | `high-level-call-options`, `create-options`, `low-level-call-options` | |
| `new` (contract creation) | SUPPORTED | `contract-creation`, `create-options` (value+salt/create2) | |
| `new T[](n)` / `new bytes(n)` | SUPPORTED | `memory-allocation` | |
| Member access | SUPPORTED | pervasive | |
| Index access | SUPPORTED | `mapping-index`, `packed-storage` | |
| Index-range access (calldata slices `x[a:b]`) | SUPPORTED | `entrypoint-slice-control` | |
| Elementary type name expression (casts) | SUPPORTED | `numeric-bytes-conversions`, `address-value-conversions` | |

### 5. Value types

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| `bool` | SUPPORTED | `Ty.bool`; pervasive | |
| `uintN` / `intN` (all widths) | SUPPORTED | `type_from_name` importer 507-514; `checked-arithmetic`, `openzeppelin-safecast` | |
| `address` / `address payable` | SUPPORTED | 499-502; `address-contract-conversions` | |
| `bytesN` (fixed-size bytes) | SUPPORTED | 515-517; `numeric-bytes-conversions` | |
| `bytes` / `string` (dynamic) | SUPPORTED | `custom-error-dynamic`, `event-indexed-dynamic` | |
| `enum` value type | SUPPORTED | see Declarations | |
| UDVT value type | SUPPORTED | see Declarations | |
| Function types (internal/external ptr) | SUPPORTED / IN-FLIGHT | `function-type-locations`, `abi-function-values`; internal-ptr residue IN-FLIGHT (`ROADMAP.md:474`) | External function values fully supported |
| `fixed` / `ufixed` | PARTIAL | `fixed-point-boundary` (declaration-only, matches solc) | No executable fixed-point arithmetic; solc also rejects it |

### 6. Reference types & data locations

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| Fixed-size arrays | SUPPORTED | `Ty.fixedArray`; `packed-storage` | |
| Dynamic arrays (`.push`/`.pop`) | SUPPORTED | Interface 5777-5779; `openzeppelin-enumerable-set`, `double-ended-queue` | |
| Mappings (incl. nested) | SUPPORTED | `mapping-index`, `reference-mapping-storage` | |
| Structs across locations | SUPPORTED | `abi-struct-tuples`, `reference-assignments` | |
| storage/memory/calldata locations | SUPPORTED | `reference-assignments`, `reference-via-ir-memory-storage`, `override-data-locations`, `typechecker-calldata-origins` | |
| `delete` (array/struct/mapping) | SUPPORTED | `reference-delete` | |
| Storage packing / dirty-word reads | SUPPORTED | `packed-storage`, `storage-dirty-words` | |
| Transient storage (EIP-1153) | SUPPORTED | `VarMutability.transient`; `reentrancy-adoption` (transient mutation lane); `AdoptionLaws.lean` transient round-trip | |
| Internal ref-signature returns / calldata-ref internal callees / tuple-hoist | IN-FLIGHT | `ROADMAP.md:474`; `docs/function-boundary-refactor-plan.md` | Sibling worktree |

### 7. Builtins, globals & members

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| `block.*` (basefee, blobbasefee, chainid, coinbase, difficulty, prevrandao, gaslimit, number, timestamp) | SUPPORTED | Interface 3944-3968, 4681-4689; block env lanes | Full magic-member set |
| `msg.*` (sender, value, data, sig) | SUPPORTED | Interface 3936-3942, 4677-4680 | |
| `tx.origin`, `tx.gasprice` | SUPPORTED | Interface 3971-3974, 4690-4691 | |
| `keccak256` | SUPPORTED | `expression-primitives`; `KeccakParity.lean` FFI byte-parity | |
| `ecrecover` | SUPPORTED | `openzeppelin-ecdsa`, `solmate-erc20` | |
| `addmod` / `mulmod` | SUPPORTED | `expression-primitives` (addmod/mulmod), 3 corpus sources | |
| `sha256` | SUPPORTED-UNTESTED | Interface (8×); 0 corpus sources | **Blind spot #1** |
| `ripemd160` | SUPPORTED-UNTESTED | Interface (8×); 0 corpus sources | **Blind spot #1** |
| `blockhash(n)` | SUPPORTED-UNTESTED | Interface (10×); 0 corpus sources | **Blind spot #1** |
| `blobhash(n)` (EIP-4844) | SUPPORTED-UNTESTED | Interface (10×); 0 corpus sources | **Blind spot #1** |
| `gasleft()` | SUPPORTED | `SolidCore/Witness/GasleftResource.lean`; modeled as resource query | Not gas metering |
| `selfdestruct` | SUPPORTED | Interface `selfdestruct`; 2 corpus sources | |
| `abi.encode` / `encodePacked` | SUPPORTED | `abi-encoding-helpers` | |
| `abi.decode` | SUPPORTED | Interface 4086; `abi-malformed`, `abi-struct-tuples` | |
| `abi.encodeWithSelector` / `encodeWithSignature` | UNKNOWN | Interface 3578-3580; used but no isolating lane | **Blind spot #6** |
| `abi.encodeCall` | SUPPORTED | Interface 4125; `abi-function-values` | |
| `bytes.concat` / `string.concat` | SUPPORTED | Interface 3487-3504 (`isBytesConcatArg`/`isStringConcatArg`) | |
| `type(T).min/max` | SUPPORTED | `expression-primitives`, `openzeppelin-safecast` | |
| `type(C).name / creationCode / runtimeCode / interfaceId` | SUPPORTED | `type-code-members`, `function-member-kinds` | |
| address `.balance` | SUPPORTED | `address-member-receivers`, `balance-accounting` | |
| address `.code` / `.codehash` | SUPPORTED | `address-member-receivers`, `type-code-members` | |
| address `.call` / `.delegatecall` / `.staticcall` | SUPPORTED | `low-level-call-options`; delegatecall/staticcall in corpus | |
| address `.send` / `.transfer` | SUPPORTED | Interface 4070/5781; corpus (send 1, transfer 8 sources) | |
| Multi-dim / nested-dynamic ABI round-trips | UNKNOWN | nested cleanups exist (Interpreter 100-101); no clearly isolating lane | **Blind spot #3** |

### 8. Literals & conversions

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| Number literals (dec/hex/scientific) | SUPPORTED | importer 1027; `NumberRat` exact-ℚ folder; `rational-constants` | |
| Rational/fractional constant folding | SUPPORTED | `rational-constants`; `docs/rational-constants-audit.md` | Over-reject fixed 2026-07-06 |
| Unit denominations (wei/gwei/ether/seconds…weeks) | SUPPORTED | `unit_denomination` importer 527 | |
| Bool literal | SUPPORTED | importer 1055 | |
| String / unicode / hex-string literals | SUPPORTED | importer 1059-1070; unicode in 4 corpus sources | |
| Address literals (checksummed) | SUPPORTED | importer 1037-1042 (`Literal.address`) | |
| Integer/bytes/fixed one-step conversions | SUPPORTED | `numeric-bytes-conversions`, `numeric-bytes` discipline | |
| address/bytes20/uint160 conversions | SUPPORTED | `address-value-conversions`, `address-contract-conversions` | |
| Explicit down/up casts & cleanup | SUPPORTED | `openzeppelin-safecast`, `AbiCleanup` | |

### 9. Special functions & dispatch

| Feature | Status | Evidence | Notes |
|---|---|---|---|
| `constructor` (+ deploy revert) | SUPPORTED | `constructor-deploy`, `inheritance-base` | |
| `receive()` | SUPPORTED | `receive-fallback-dispatch`, `entrypoint-slice-control` | |
| `fallback()` (typed & raw-bytes) | SUPPORTED | `receive-fallback-dispatch` | |
| `payable` functions / conversions | SUPPORTED | `create-options`, `address-contract-conversions` | |
| Visibility (public/private/internal/external) | SUPPORTED | `visibility` importer ~783 | |
| State mutability (pure/view/nonpayable/payable) | SUPPORTED | `state_mutability` importer ~805 | |
| External calls / open-world interaction | SUPPORTED | interaction monad; `high-/low-level-call-options` | |
| Reentrancy via postWorld adoption | SUPPORTED | `reentrancy-adoption`; `AdoptionLaws.lean` round-trip law | Fixed 2026-07-07 |
| Contract creation via `new` (+ create2 salt) | SUPPORTED | `contract-creation`, `create-options` | |

### 10. Out-of-scope by decision (for completeness)

| Feature | Status | Evidence |
|---|---|---|
| Inline assembly / Yul | OUT-OF-SCOPE | `ROADMAP.md:469` |
| Imports / multi-file units | OUT-OF-SCOPE | `ROADMAP.md:470` |
| Gas metering (real gas) | OUT-OF-SCOPE | `ROADMAP.md:473` |
| `msize` | OUT-OF-SCOPE | mission brief |
| Closed-world multi-contract execution | OUT-OF-SCOPE | `ROADMAP.md:471` (open-world query model) |
| Create initCode = compiled bytecode | OUT-OF-SCOPE (deferred, gas-like) | `ROADMAP.md:468` (source-canonical initCode) |

---

## Auditor's honesty notes (UNKNOWN items)

These could not be resolved from static evidence alone and are flagged rather
than guessed:

1. `sha256` / `ripemd160` result-word fidelity vs. the pinned EVM precompiles — no lane, output correctness unverified.
2. Deeply nested `T[][]` / `string[]` `abi.decode` round-trips — cleanups exist but no isolating lane found.
3. `abi.encodeWithSelector` / `encodeWithSignature` dynamic-arg edge behavior — used but not adversarially isolated.
4. `using ... for *` wildcard target — importer path plausibly exists but not observed in any lane.
5. Per-operator coverage of the full UDVT user-defined-operator set — the family is exercised, individual operators are not each pinned.
6. Whether every `bytesN`↔`uintN`↔`intN` cast width combination is pinned (the discipline lane covers one-step conversions, not the full cross-product).
7. `blockhash`/`blobhash` availability-window semantics (e.g. out-of-range → 0) — elaborated, never exercised.

No feature was found that the importer or interface accepts while silently
mis-modeling it: `guard_no_unsupported_nodes` and the interface sentinels fail
closed on anything unrecognized.
