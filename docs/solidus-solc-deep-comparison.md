# Exhaustive Solidus-vs-solc 0.8.35 feature comparison

A category-by-category sweep of **every** feature category solc 0.8.35 exercises
in its own conformance suites, checked against **Solidus** (this repo's executable
Lean Solidity semantics: `SolidCore/Solidity/{Interface,Interpreter,TypeCheck,Checked,ABI}.lean`,
importer `scripts/solc_ast_to_lean_source.py`, corpus `tests/forge-harness/manifest.json`).

**Method.** The completeness spine is solc's own test tree at the exact pinned tag
(`/Users/dan/Projects/solidity-src`, `v0.8.35`, READ-ONLY):

- `test/libsolidity/semanticTests/` — **68** categories enumerating runtime behaviours.
- `test/libsolidity/syntaxTests/` — **71** categories enumerating accept/reject rules.

For each of the 139 categories we read a representative sample of the `.sol`
sources and their isoltest expectations, extracted the rule/behaviour solc
enforces, and checked whether Solidus handles it — with evidence from the Lean
sources and whether a corpus lane exercises it. Highest-risk families (arithmetic
edges, cleanup, ABI codec, conversions, member lookup, inheritance/override,
function types, data locations, storage layout, try/catch, events, errors,
denominations, literals, calldata element validation, **user-defined operators**)
were read line-by-line on **both** sides.

Read-only review: nothing was built or run; the corpus/replay were not exercised.
Findings are **CONFIRMED** (read definitively on both sides) or **INFERRED**
(deduced from source, wants a probe). This sweep builds on two prior reviews:

- `docs/solidity-feature-coverage.md` — AST node-kind-level audit.
- `docs/solc-source-coverage-review.md` — sub-node review (S1–S5, A1–A4, C1–C6).

All of that second doc's findings are **fixed and merged** at HEAD `40c63e3`; §1
verifies each reads as fixed before this review cites it as settled.

---

## Executive summary

**Headline: this exhaustive sweep found ONE new wrong-value soundness gap —
`G1`, user-defined operators — that both prior reviews missed, plus a cluster of
acceptance over-accepts (led by `G2`, `msg.value` in view functions).**

**G1 — user-defined operators (`using {f as +} for T`, incl. all UDVT operators)
are silently evaluated as the *built-in* operator on the underlying type, not by
running the operator function.** The importer drops solc's resolved operator
reference (`('BinaryOperation','function')`/`('UnaryOperation','function')` sit in
`ANALYSIS_SCALAR_FIELDS`, dropped, `solc_ast_to_lean_source.py:34`); the node
lowers to a plain `Expr.binary op`, and the interpreter applies
`BinaryOp.apply context.checked op` on the raw words (`Interpreter.lean:6153`,
unary `:6000`). Whenever an operator body differs from the builtin — a fixed-point
`*` = `(a*b)/1e18`, a saturating/recursive/custom body, or a body whose
checked-ness differs from the caller's `unchecked` context — Solidus computes the
wrong value **and** accepts the program. It has passed only because every existing
UDVT-operator lane defines the operator body to equal the builtin (`20+22=42`, OZ
`Time.Delay`), so substitution coincidentally agrees. This **corrects the prior
audit's "using_operator SUPPORTED" row** (`solidity-feature-coverage.md` row 131).
CONFIRMED on both sides. Probe: import
`operators/userDefined/fixed_point_udvt_with_operators.sol`,
`applyInterest(500e18, 0.1e18)` → solc `550e18`, Solidus ≈`5e37` (builtin multiply).

The one value path the prior review left as most suspicious — calldata
narrow-int/enum aggregate element cleanup (S2) — was instead read to the bottom
and found **fully faithful**: solc validates every calldata value read on
*access* (`readFromMemoryOrCalldata` `_fromCalldata=true` → `calldataload` +
`validator(revertOnFailure)`, `YulUtilFunctions.cpp:4552-4553`, used for struct
members `IRGeneratorForStatements.cpp:2127` and array elements `:2435`), and
Solidus's lazy `AbiCleanup.forceValue` reverts on first use
(`Interpreter.lean:341-343,357-382`) — same lazy timing, same empty revert. A
CONFIRMED negative that also corrects the prior doc's S2 observable.

### Methodology counts

| Suite | Categories walked | Faithful / covered | Partial · over-accept/reject | Out-of-scope by decision |
|---|---|---|---|---|
| semanticTests | 68 | 54 | 5 | 9 |
| syntaxTests | 71 | 45 | 14 | 12 |
| **Total** | **139** | **99** | **19** | **21** |

### Ranked NEW findings (SOUNDNESS first)

**Wrong-value soundness (highest):**

1. **G1 — user-defined operators run as built-ins.** WRONG-VALUE, CONFIRMED,
   corpus-reachable (any contract whose operator body ≠ builtin). `solc_ast_to_lean_source.py:34,883`; `Interpreter.lean:6000,6153`; `TypeCheck.lean:6836,6899` (types only, no dispatch).

**Acceptance-soundness (over-accept — fires only if `importedContractAccepted` is read as a certificate; never on a solc-validated corpus):**

2. **G2 — `msg.value` accepted in `view`/`nonpayable` functions.** CONFIRMED,
   broadly reachable. solc TypeError 5887 (payable-only); `TypeCheck.lean:5222-5226`
   only calls `requireStateReadAllowed` (fails only for `pure`), no payable gate.
3. **G3 — `==`/`!=` accepted on reference types** (struct/array/bytes/string/mapping).
   CONFIRMED. solc TypeError 2271; `TypeCheck.lean:6918-6928` checks only reflexive
   mutual convertibility.
4. **G4 — constant out-of-bounds index on `bytesN` / fixed-size array not
   rejected.** CONFIRMED. solc TypeError 1859/3383 (compile-time); Solidus
   accepts, runtime Panics 0x32. `TypeCheck.lean:5478-5490`.
5. **G5 — bare `return;` accepted with named returns.** CONFIRMED. solc TypeError
   6777; `TypeCheck.lean:8118-8123`.
6. **G6 — `super.f()` resolves to an unimplemented (abstract) base fn.** INFERRED.
   solc TypeError 9582; `TypeCheck.lean:1479-1494, 12023-12046`.
7. **G7 — `emit A.g()` (non-event, member callee) not event-validated.** INFERRED.
   solc TypeError 9292; `TypeCheck.lean:8301-8308`.
8. **G8 — `revert E(args)` with a same-arity shadowing member.** INFERRED, obscure.
   solc TypeError 1885; `TypeCheck.lean:~7761`.
9. **G9 — inline array literal of mapping type `[m]`.** CONFIRMED-code/INFERRED-obs.
   `TypeCheck.lean:6811-6825` builds `array mapping` with no location bar.
10. **G10 — `msg.data` in `receive()` not rejected.** INFERRED, harmless. solc
    TypeError 7139.
11. **G11 — cross-contract `creationCode`/`runtimeCode` cycle undetected.**
    INFERRED, esoteric. solc TypeError 7813; no whole-program cycle pass.
12. **G12 — identifier name `_` not reserved.** INFERRED, minor (unreachable via
    import). solc DeclarationError 3726.

**Completeness (over-reject valid programs — harmless):**

13. **G13 — nested tuple LHS `(((a,),)) = ((1,2),3);`.** CONFIRMED.
    `TypeCheck.lean:7522-7539` (no recursion into nested targets).
14. **G14 — storage array assignment with base-convertible / shorter source.**
    CONFIRMED. solc `Types.cpp:1640-1648` (zero-fills tail); `Ty.canImplicitlyConvert`
    has no array arm (`TypeCheck.lean:1049-1100`).
15. **G15 — ternary-of-literals loses `uint8` mobile common type → narrowing
    assign over-rejected.** CONFIRMED (same family as S3, distinct observable —
    reject vs runtime-panic). `TypeCheck.lean:3987-3991, 1319-1331`.
16. **G16 — `try` on a library/using-for call over-rejected.** INFERRED.
    `TypeCheck.lean:8222-8256` requires a contract value path.

**Untested (handled, no differential lane):**

17. **G17** — storage-default/ctor-stored uninit internal fn ptr → `Panic(0x51)`
    (only local-uninit laned). `Interpreter.lean:7282-7292`.
18. **G18** — try/catch binding of a multi-slot external-fn-ptr return. `:7174-7236`.
19. **G19** — mutability-relaxing overrides (`virtual`→`view`/`pure`); runtime-identical.
20. **G20** — `using ... for *` wildcard imported (`solc_ast_to_lean_source.py:1790-1795`,
    `target := none`) but unexercised (resolves prior UNKNOWN #4).
21. **G21** — C99 block-scope activation incl. `uint x = x;` self-init; sequential
    `Frame` push/pop, no lane. `Interpreter.lean:947-1013`.
22. **G22** — saltedCreate create2 *address prediction* (needs initcode-as-bytecode;
    OOS-adjacent). Several modifier paths (return-capture, override, ctor-modifier)
    modeled but unlaned.

Minor: constant folding uses exact ℚ with no size cap, so `2**4096 * 0` folds
where solc rejects at its 4096-bit intermediate limit — harmless (any real
type-fit rejects downstream).

---

## 1. Verification of prior-review findings (all read as FIXED)

| ID | What | Fixed evidence | Lane |
|---|---|---|---|
| S1 | String literal → UTF-8 (was codepoints) | `Interface.lean:2956 stringUtf8Bytes`, used `:2991-2994, 3497-3502` | `utf8-string-literal` |
| S2 | Memory-aggregate narrow element eager ABI validation | `AbiCleanup.memoryEager` `Interface.lean:16944,19528`, `Interpreter.lean:340`; calldata stays lazy-on-access (faithful) | `abi-memory-eager` |
| S3 | Ternary-in-`encodePacked` common-type width | fixed | `packed-ternary-width` |
| S4 | `Panic(0x41)` oversized alloc now unconditional at 2^64-1 | `Interpreter.lean:1685` | witness/lane |
| S5 | `Panic(0x22)` malformed long-form storage byte-array | `Interpreter.lean:2871-2886` | `storage-dirty-words` |
| A1–A4 | signed/unsigned implicit, mixed-sign common type, signed↔bytesN, contract base→derived | `TypeCheck.lean:1148-1173` tightened | `signed-unsigned-contract-conversions`, `openzeppelin-signed-math` |
| C1 | `string.length` over-accept | fixed | pinned |
| C2 | `type(C).interfaceId`/creationCode kind-gating | `0c42660` | pinned |
| C3 | `encodePacked(bytes[]/string[])` | `0c42660` | pinned |
| C4 | Constant `%` with negative operand | `Interface.lean:2788-2797` `Int.tmod` | `rational-constants` |
| C5 | `bytesN.length` static type (benign) | fixed | — |

`sha256`/`ripemd160`/`blockhash`/`blobhash` (node-kind audit blind-spot #1) now
have differential lanes (`1b3525e`). Corpus is now **121 lanes**.

---

## 2. NEW findings (both-sides file:line + probe)

### G1 — user-defined operators execute as built-ins — WRONG-VALUE SOUNDNESS, CONFIRMED
- **solc:** the operator body may differ arbitrarily from the builtin.
  `operators/userDefined/fixed_point_udvt_with_operators.sol` defines `*` as
  `(a*b)/1e18` → `applyInterest(500e18,0.1e18) == 550e18`;
  `recursive_operator.sol` redefines `~` as a recursive countdown →
  `testUnary(1)==0`; `checked_operators.sol` runs the operator body *checked* even
  inside a caller's `unchecked` block → Panic 0x11.
- **Solidus:** importer drops the resolved operator `function` reference
  (`ANALYSIS_SCALAR_FIELDS`, `solc_ast_to_lean_source.py:34`); `using_operator`
  maps the symbol straight to a builtin (`+`→`BinaryOp.add`, `:883-899`, used at
  `:1736`); the node emits as `Expr.binary op`/`Expr.unary op`; the interpreter
  applies `BinaryOp.apply context.checked op …` (`Interpreter.lean:6153`) /
  `op.apply` (`:6000`) on the underlying words. `TypeCheck.resolveUsingBinaryOperator?`
  (`:6836,6899`) sets only the *result type*, never rewrites into a call. No
  operator-dispatch pass exists.
- **Reachable:** any contract with a user-defined operator whose body ≠ builtin
  (fixed-point/saturating/custom libraries, or checked-vs-unchecked mismatch).
  Both accepts the program and returns the wrong value.
- **Fix sketch:** importer must preserve the resolved `function` reference;
  evaluator must dispatch `Expr.binary`/`Expr.unary` on UDVT operands through it.

### Acceptance-soundness (over-accept)

**G2 — `msg.value` in `view`/`nonpayable` — CONFIRMED, most reachable acceptance item.**
- solc: `syntaxTests/functionCalls/msg_value_non_payable.sol` → TypeError 5887;
  rule `ViewPureChecker.cpp:287-291` (`msg.value`/`callvalue()` only in payable or
  internal).
- Solidus: `TypeCheck.lean:5222-5226` — the `msg.<member>` arm calls
  `requireStateReadAllowed` for non-`data`/`sig` members; `mutabilityAllowsStateRead`
  (`:1668`) fails only for `pure`, so `view`/`nonpayable` pass. No payable gate.
- Probe: `function get() public view returns (uint) { return msg.value; }` — solc
  5887, Solidus accepts.

**G3 — `==`/`!=` on reference types — CONFIRMED.**
- solc: TypeError 2271. `syntaxTests/nameAndTypeResolution/{202_bytes,203_struct}_reference_compare_operators.sol`,
  `025_comparison_of_mapping_types.sol`. `==`/`!=` permitted only on value types,
  contracts, enums, addresses, function pointers.
- Solidus: `TypeCheck.lean:6918-6928` requires only mutual implicit convertibility,
  reflexive (`:1050`); relational `< > <= >=` correctly guarded by `relationalTy`
  (`:6916`) but equality is not.
- Probe: `struct S{uint a;} S x; S y; bool b = x == y;` → solc 2271, Solidus accepts.

**G4 — constant OOB index on `bytesN`/fixed array — CONFIRMED.**
- solc: `syntaxTests/indexing/fixedbytes_out_of_bounds_index.sol` (TypeError 1859,
  `bytes4 b; b[5]`), `array_out_of_bounds_index.sol` (TypeError 3383, `uint[3] a;
  a[5]`) — compile-time.
- Solidus: `bytesN` index arm (`TypeCheck.lean:5478-5482`) and fixed-array arm
  (`:5483-5490`) only `expectAssignableTo(uint256)`; no constant `index < N` check.
  Accepted at typecheck; runtime Panics 0x32.

**G5 — bare `return;` with named returns — CONFIRMED.**
- solc: TypeError 6777 for `return;` whenever the return list is non-empty, even
  when named (`syntaxTests/returnExpressions/single_return_mismatching_number_named.sol`).
- Solidus: `checkReturnExprs` (`TypeCheck.lean:8118-8123`) accepts `none` when
  `returnNamesAllNamed`. Value well-defined (returns named values); low real-soundness.

**G6 — `super.f()` to unimplemented base — INFERRED.** solc TypeError 9582
(`syntaxTests/super/unimplemented_super_function.sol`); `FunctionSig` has no
has-body flag (`TypeCheck.lean:1479-1494`), abstract sigs enter `env.superFunctions`
(`:12023-12046`), super resolution (`:6517`) matches by name+args.

**G7 — `emit A.g()` non-event member callee — INFERRED.** solc TypeError 9292
(`syntaxTests/emit/emit_non_event.sol` tests the simple-name form); `checkEventEmission`
(`TypeCheck.lean:8301-8308`) validates event identity only for `call (ident name) args`;
member callees fall through. (Paired risk: may over-reject a legitimate `emit A.e(...)`.)

**G8 — `revert E()` with shadowing member — INFERRED, obscure.** solc TypeError 1885
(`syntaxTests/revertStatement/using_function.sol`); `checkCustomErrorArgs`
(`TypeCheck.lean:~7761`) resolves against `env.errors`, ignoring an in-scope
same-name function.

**G9 — inline array literal of mapping — CONFIRMED-code / INFERRED-obs.** solc
forbids mappings in inline arrays; `Expr.array` arm (`TypeCheck.lean:6811-6825`)
computes a common element type and builds `Ty.array mapping (some 1)` with no
mapping/location bar. Probe: with storage `mapping(uint=>uint) m;`, expression `[m]`.

**G10 — `msg.data` in `receive()` — INFERRED, harmless.** solc TypeError 7139
(`syntaxTests/receiveEther/msg_data_in_receive.sol`); no gate; receive has empty
calldata so the observable is benign.

**G11 — cross-contract code cycle — INFERRED, esoteric.** solc TypeError 7813
(`syntaxTests/metaTypes/codeAccessCyclic.sol`); creationCode/runtimeCode gated only
on kind/self-ancestor (`TypeCheck.lean:~5335`), no whole-program cycle analysis.

**G12 — `_` not reserved — INFERRED, minor.** solc DeclarationError 3726
(`syntaxTests/underscore/{in_function,in_modifier}.sol`); only the
`modifierPlaceholder` AST node is handled. Unreachable via import (solc rejects first).

### Completeness (over-reject)

**G13 — nested tuple LHS — CONFIRMED.** solc accepts `(((a,),)) = ((1,2),3);`
(`syntaxTests/tupleAssignments/tuple_in_tuple_short.sol`, empty expectations);
`checkTupleAssignmentTargets` (`TypeCheck.lean:7522-7539`) does not recurse into
nested tuple targets (`lvalue:=false`, `:6804`).

**G14 — storage array assignment base-convertible/shorter source — CONFIRMED.**
solc `ArrayType::isImplicitlyConvertibleTo` (`Types.cpp:1640-1648`) accepts, for a
non-pointer storage dest, an implicitly-convertible base with `dest.length ≥
src.length` (tail zero-filled): `storage/static_array_copy_cleanup.sol` (`S[5]→S[10]`),
`chop_sign_bits.sol` (`int8[]→int16[]`). `Ty.canImplicitlyConvert` has no array arm
(`TypeCheck.lean:1049-1100 → _,_ => false`); the contextual fallback also requires
`actual == expected` (`:4762-4773`). Rejected at typecheck — no mis-copy, so safe.

**G15 — ternary-of-literals loses mobile common type — CONFIRMED.** solc
`literals/ternary_operator_with_literal_types_overflow.sol` — `(t?63:255)` has
common type `uint8`, `+` runs in uint8 → Panic 0x11 even with `uint16` target.
Solidus types number literals `uint256` (`TypeCheck.lean:3987-3991`);
`exprIsUntypedNumberLiteralExpression` excludes `ternary` (`:1319-1331`), so the
`uint256` add can't narrow to `uint16` → rejects at typecheck instead of running
the panic. Same root as S3, distinct observable.

**G16 — `try` on library/using-for call — INFERRED.** solc accepts `try L.f(...)`
(`syntaxTests/tryCatch/library_call.sol`); `checkTryExternalMemberCallTarget`
(`TypeCheck.lean:8222-8256`) requires an `isContractValuePath` receiver. (Moot if
library external calls are unsupported elsewhere.)

### Untested (G17–G22)

- **G17** storage-default/ctor-stored uninit internal fn ptr → `Panic(0x51)`
  (`Interpreter.lean:7282-7292`; only local-uninit laned). Probe: unassigned
  `function() internal storedFn` state var, call it → `FAILURE, 0x4e487b71, 0x51`.
- **G18** try/catch binding of a multi-slot external-fn-ptr return (`:7174-7236`);
  probe replicates `tryCatch/return_function.sol`.
- **G19** mutability-relaxing overrides (`virtual`→`view`/`pure`); runtime-identical.
- **G20** `using ... for *` wildcard imported (`solc_ast_to_lean_source.py:1790-1795`)
  but unexercised (resolves prior UNKNOWN #4).
- **G21** C99 block-scope activation incl. `uint x = x;` self-init
  (`Interpreter.lean:947-1013`); `scoping/c99_scoping_activation.sol`.
- **G22** saltedCreate address prediction (needs initcode-as-bytecode, OOS-adjacent);
  modifier return-capture/override/ctor-modifier paths modeled, unlaned.

---

## 3. semanticTests coverage matrix (68 categories)

Legend: **S** SUPPORTED (lane-backed) · **SU** SUPPORTED-UNTESTED · **P** PARTIAL
· **OA/OR** over-accept/over-reject · **SND** wrong-value soundness gap · **OOS**.

### Group A — ABI / arithmetic / conversions (line-by-line)

| Category | St | Evidence |
|---|---|---|
| abiEncodeDecode | S | head/tail + decode-bounds faithful (`ABI.lean:369-419`); offset-overflow → empty `drop` → revert |
| abiEncoderV1 | S | encode/decode via `ABI.lean`; legacy non-viaYul dirty-bool tolerance is OOS codegen |
| abiEncoderV2 | S | calldata nested/dynamic decode+re-encode; struct-element cleanup = S2 (faithful) |
| accessor | S | public state-var/const getters |
| arithmetics | S | checked/unchecked add/sub/mul/div/mod/exp; signed `INT_MIN/-1`→0x11 (`Interpreter.lean:5319`) |
| array | S | `bytes→bytesN` first-N right-padded no revert (`Interpreter.lean:603-611`); push/pop, inline array |
| builtinFunctions | S | keccak/ecrecover/addmod/mulmod + sha256/ripemd160/blockhash/blobhash now laned |
| calldata | S | arrays/slices/structs decode+bounds; dirty narrow element reverts on access (faithful) |
| cleanup | S | narrow-exp cleanup faithful (`exp_cleanup*.sol`); downcast tests viaYul+asm (OOS) |
| constantEvaluator | S/P | int const div truncates-to-zero; C4 negative `%` fixed; no 4096-bit cap (harmless OA) |
| constants | S | file-level/const-eval array lengths; const string via S1 UTF-8 |
| constructor | S | base-ctor arg **evaluation order** faithful (base-first inline, `Interface.lean:19532-19556`) → 1,3,2,4 |
| conversions | S | implicit/explicit tables match `Types.cpp`; A1–A4 fixed |

### Group B — types / functions / inheritance / events / errors

| Category | St | Evidence |
|---|---|---|
| ecrecover | S | precompile as STATICCALL (`Interpreter.lean:2299`); `openzeppelin-ecdsa`, `solmate-erc20`; invalid→0 |
| enums | S | `enum-conversions`; explicit overflow→0x21 (`:5551-5570`); storage vs calldata validator distinction |
| errors | S | `custom-error(-dynamic)`; selector=keccak(canonical sig); `require(cond,E())`; named-arg reorder |
| events | S | `event-emitter`, `event-indexed-dynamic`; anonymous→no topic0 (`:7442`); indexed refs hashed (`:4485`); indexed-count limit |
| exponentiation | S | signed-base via `checkedSignedExp` (`:5350`, W3 fixed); `0**0`→1; unchecked two's-complement wrap |
| expressions | S | full binary/unary/assign/ternary/tuple/index |
| fallback | S | `receive-fallback-dispatch`; typed + raw-bytes; override |
| freeFunctions | S | importer `freeFunction`→`function`; `source-declarations` |
| functionCall | S | `function-calls`, high/low-level call options, salted create |
| functionSelector | S | `.selector` on `A.f`/`a.f` (`function-member-kinds`) |
| functionTypes | S | `function-type-locations`, `abi-function-values`; internal ptr in mapping/storage; 0x51 zero-init; `.selector`/`.address` gated |
| getters | S | value getters; multi-key mapping; struct getter omits mapping+array (`:2358,2396`) |
| immutable | S | assign-at-decl, read-in-ctor, signed immutable |
| inheritance | S | `inheritance-base`, `callable-identity` (C3/super/virtual/override, multi-base) |
| integer | S | `checked-arithmetic`, `openzeppelin-safecast`; all widths; 0x11/0x12 |
| interfaceID | S | `interfaceId?` = XOR of function selectors (`:7537`); events excluded |

### Group C — libraries / literals / storage / modifiers / operators / structs / UDVT / using

| Category | St | Evidence |
|---|---|---|
| libraries | S | internal-lib inlining + using-for across OZ/Uniswap lanes; delegatecall kind (`Interpreter.lean:1570,2237`); guard tests are asm (OOS) |
| literals | S | `rational-constants`, `literal-cast-conversions`; `NumberRat` exact folding (`Interface.lean:2655-2799`) |
| memoryManagement | P/OOS | 4/5 solc tests read `mload(0x40)` (asm, OOS); observable part `memory-allocation(-overflow)` |
| metaTypes | S | `type(X).name`→`Ty.typeInfoExpr?` (`Interface.lean:3466`); `importedTypeNameMemberSemantics` |
| modifiers | S | placeholder lowering + return-capture (`Interpreter.lean:8059`); some paths UNTESTED (G22) |
| operators (builtin) | S | `BinaryOp.apply`, `sar/shr/shl` (`:5383`); transient inc/dec (`:913-924`) |
| **operators (user-defined)** | **SND** | **G1 — run as builtins, not the operator function** |
| payable | S | entry callvalue check precedes modifiers (`:8571,8648`); `no_nonpayable_circumvention_by_modifier` |
| receive | S | empty-calldata→receive→fallback→empty-revert + value gating (`ABI.lean:633-708`) |
| reverts | S | Panic 0x21 enum, custom errors, `Error(string)`; `custom-error`, `terminal-statements` |
| revertStrings | P/OOS | debug-string payloads OOS; production empty-revert modeled (`ABI.lean:536-547`) |
| saltedCreate | P | create2 salt (`create-options`); address *prediction* needs initcode-bytecode (G22, OOS) |
| scoping | SU | sequential `Frame` push/pop (`:947-1013`); no C99-activation lane (G21) |
| specialFunctions | S | `encodeWithSignature` literal→compile-time selector, runtime→`keccak256(sig)[:4]` (`Interface.lean:4137-4154`) |
| state | S | full `block.*/msg.*/tx.*/blockhash/blobhash/gasleft` (`:1824-1907`); blockhash 256-window |
| statements | S | do-while/for + break/continue (`:8149`); `loop-control` |
| storage | S | byte-level `packedScalar` + sign-extend-on-read (`:1316-1376,3323`); `packed-storage`, `storage-dirty-words`, `storage-bytes-encoding` |
| strings | S | UTF-8 plain/unicode/hex via `stringUtf8Bytes`; `utf8-string-literal` (S1 fixed) |
| structs | S | cross-location nested copies, packed-struct delete, delete-preserves-mapping (`reference-assignments`, `reference-mapping-storage`) |
| userDefinedValueType | S except ops | wrap/unwrap/storage/mapping-key sound; **operators hit G1** |
| using | S except ops | member-fn resolution sound (`TypeCheck.lean:3926`); **`using {f as +}` operator dispatch is G1** |

### Group D — control / meta / misc

| Category | St | Evidence |
|---|---|---|
| tryCatch | S | Error/Panic/bare/low-level dispatch; no-match re-reverts raw (`Interpreter.lean:7195-7224,8286-8299`); `try-catch` |
| types | S | conversion-cleanup chains (A1–A4 fixed) |
| variables | S | default init per type; transient state vars (`reentrancy-adoption`); dirty-bool tests asm (OOS) |
| various | S | selfdestruct/code-access/gasleft/tuples; asm cases OOS |
| virtualFunctions | S | virtual/override/super + C3 (`callable-identity`); mutability-relaxing override UNTESTED (G19) |
| underscore | S | `_`=`modifierPlaceholder` (importer 1367); function-name-`_` UNTESTED |
| uninitializedFunctionPointer | S/SU | local-uninit → 0x51 laned; storage/ctor-stored UNTESTED (G17) `:7282-7292` |
| deployedCodeExclusion | OOS | runtime-bytecode/codesize — codegen, asm-observed |
| shanghai | S | PUSH0-era codegen; behaviour identical |
| storageLayoutSpecifier | OOS | `layout at N` fail-closed at import (`py:410-433`); asm-observed |
| smoke / isoltestTesting | OOS | harness fixtures |
| inlineAssembly / viaYul | OOS | Yul / codegen backend |
| externalContracts | OOS | multi-contract closed-world |
| externalSource / multiSource | OOS | imports/multi-file (`ROADMAP.md:470`) |
| experimental / optimizer | OOS | SMT-experimental / codegen |

---

## 4. syntaxTests coverage matrix (71 categories)

### Group syntax-2 (accept/reject rules, read deeply)

| Category | St | Evidence |
|---|---|---|
| nameAndTypeResolution | S | redeclaration/overload-ambiguity/override/enum-contract conv/using-for/super-scope (`TypeCheck.lean:11905,2239,9209,1049`) |
| operators | OA | arith/bitwise/shift OK; **G3** `==`/`!=` no ref-type guard (`:6918-6928`) |
| shifts | S | signed/negative shift amount rejected (`expectUnsignedInteger`, `:6948`) |
| types | S | implicit/explicit tables match; bytesN↔uintN equal-width+unsigned; UDVT never convertible |
| tupleAssignments | OR | arity+per-slot OK; **G13** nested tuple LHS over-rejected (`:7522-7539`) |
| userDefinedValueType | S | wrap/unwrap arity+type; explicit `MyT(x)`/UDVT↔UDVT rejected (`5844,1434`) |
| unchecked | S | nested `unchecked` rejected (`:8820`); placeholder-in-unchecked rejected |
| visibility | S | bare-internal-call-to-external rejected; internal/private excluded from external resolution (`5646,2729`) |
| scoping | S | init-before-decl checked; block scope isolated; inherited shadowing error (`8845,8684,12055`) |
| virtualLookup | S | `checkOverridable` requires base `virtual`; full return/param/location/visibility/mutability compat (`9209-9236`) |
| super | P | normal dispatch OK; **G6** resolves unimplemented abstract base fn (`12023-12046`) |
| modifiers | S | missing-`_`/unimplemented-must-be-virtual/library-not-virtual/return-in-modifier rejected (`11200,11196`) |
| underscore | P | `_` outside modifier rejected; **G12** `_` not reserved as identifier |
| using | S | target-type gating + self-param location compat; library-target-must-be-library (`3634,3536`) |
| constructor | S | name/visibility/virtual/override/returns/mutability/param-location + multiple-ctor (`9865-9908,11922`) |
| controlFlow | S | genuine storage-pointer definite-assignment dataflow pass (`checkPointerReturnDefiniteAssignment`, `10174-10930`); unreachable=warning (OOS) |
| specialFunctions | S | abi-encodable arg checks; keccak/sha bytes-like; encodeCall arity/type (`4135-4972`) |
| receiveEther | S | no-params/empty-returns/external/payable (`9909-9923`); **G10** msg.data-in-receive not gated |
| fallback | S | external, nonpayable/payable, `()` or `(bytes calldata)→(bytes memory)` (`9924-9945`) |
| returnExpressions | OA | arity/type OK; **G5** bare `return;` with named returns (`8118-8123`) |
| variableDeclaration | OOS | parser/reserved-name (SyntaxError) |
| unusedVariables | OOS | Warning-only |
| structs | S | recursion-cycle rejection matches solc; field library-type + unique-name (`11300,11345`) |
| enums | S | 1..256 members, unique (`11365`) |
| errors | S | no-mapping/ABI-encodable/no-location/no Error-Panic-redefine (`11266`) |
| events | S | indexed ≤3 (≤4 anonymous)/ABI-encodable/no-mapping/unique (`11233,11261`) |
| emit | P | simple-name non-event rejected; **G7** member/qualified form not event-validated (`8301-8308`) |
| string | S | prior C1 `string.length` fixed |
| revertStatement | S | `revert Name(...)` resolved in `env.errors`; event/struct rejected; **G8** shadowing edge |
| tryCatch | S | external-target discipline; exact catch headers; duplicate-clause rejection (`8258,8606,8653`); **G16** library-target over-reject |

### Group syntax-1 (conversion / data locations / member lookup / literals)

| Category | St | Evidence |
|---|---|---|
| conversion | S (beyond A1–A4) | `Ty.canExplicitlyConvert` (`:1356-1440`); `bytes→bytesN` matches `Types.cpp:1673`; string→bytesN rejected; addr/uint160/bytes20 exact-width |
| denominations | S | importer whitelist (`solc_ast_to_lean_source.py:51`) = {wei,gwei,ether,seconds,minutes,hours,days,weeks}; `finney`/`szabo`/`years` absent → `fail()` |
| functionTypes | S | mutability lattice (`:1033-1047`); exact visibility/location (`:1087-1099`); internal-payable + external-taking-internal rejected (`726-739`) |
| functionCalls | OA | call-option legality thorough (`6353-6678`); **G2** `msg.value` in view/nonpayable (`5222-5226`) |
| getter | S | `Ty.publicGetterShape?` (mapping→params, array→index, struct omits nested mapping/array) |
| metaTypes | OA (esoteric) | min/max gated (contract `.min` rejected); creationCode/runtimeCode kind-gated (C2); **G11** cross-contract cycle undetected |
| immutable | S | non-value/ref rejected (`isImmutableStateVarTypeShape` 453); external-fn immutable rejected (455-456); write only in ctor (4106/5081) |
| abiEncoder | S (v2) | encodeCall external-ptr/no-lib/no-internal/no-holes (`4556-4964`); external-fn-param mapping/internal rejected (9984-9992); abicoder-v1 OOS |
| indexing | OA | negative/huge literal index rejected (`expectAssignableTo uint256` 5472/5479); **G4** constant OOB not checked |
| memberLookup | S | `.length` non-lvalue (5424-5431); `string.length` rejected (`hasLengthMember` 4044 excludes `Ty.string`); push/pop gated to dynamic storage |
| lvalues | S | `arr.length=x` rejected; mapping-storage-copy guard (`requireNoMappingStorageCopy` 3012); `bytesN[i]` non-lvalue (5482) |
| inlineArrays | OA | inline array common-type computed; **G9** `[mappingVar]` builds `array mapping` with no bar |
| array | S | slice gated to calldata (5515); element common-type checked (6811-6825); index caveat → G4 |
| dataLocations | S | fn-param location validity (`functionDataLocationValid` 679-693); external params reject `storage` (696-702) |
| abstract / inheritance | S | immutable/override structural rules import-gated; no divergence in sampled rejects |
| literals / literalOperations | S/P | literal-fit (`typeConversionLiteralFits` 1275); constant div-by-zero/huge-exponent folding not independently deep-verified (see caveat) |
| largeTypes | P | size limits not deep-verified (likely codegen/OOS) |

### Residual syntaxTests categories (parser/codegen/OOS or folded)

| Category | St | Note |
|---|---|---|
| parsing / unterminatedBlocks / comments | OOS | pure parser; solc rejects before AST import |
| license / pragma | OOS/P | pragma handled (`PragmaDirective`); SPDX/version is preprocessing |
| imports / multiSource | OOS | multi-file (`ROADMAP.md:470`) |
| inlineAssembly | OOS | Yul |
| experimental | OOS | SMT/experimental |
| iceRegressionTests | OOS | compiler-crash regressions |
| bytecodeReferences / sizeLimits / storageLayoutSpecifier | OOS | codegen/limits |
| smoke / isoltestTesting | OOS | harness |
| duplicateFunctions | S | duplicate/overload-collision rejected (`nameAndTypeResolution` overload rules) |
| constantEvaluator / constants | S/P | see semanticTests (C4 fixed; no 4096-bit cap, harmless) |
| freeFunctions / globalFunctions | S | free-fn import; global builtins covered |
| multiVariableDeclaration | S | tuple var decls (`tuple-destructure`, `tuple-holes`) |
| viewPureChecker | S/OA | mutability enforced (`TypeCheck.lean:1670-1706,1687-1691`); **G2** is the one payable-gate gap |

---

## 5. Out-of-scope appendix (by explicit project decision — not gaps)

| Area | Decision | Reference |
|---|---|---|
| Inline assembly / Yul (`inlineAssembly`, `viaYul`, `Yul*`) | OOS | `EXCLUDED_NODE_TYPES` (`solc_ast_to_lean_source.py:30`) |
| Imports / multi-file (`imports`, `multiSource`, `externalSource`, `externalContracts`) | OOS | flattening as preprocessing; `ROADMAP.md:470` |
| Real gas metering, `msize` | OOS | gasful refinement conjunct; `gasleft` = resource query |
| Closed-world multi-contract execution, reentrancy-as-execution | OOS | open-world query + `postWorld` adoption model |
| Create initCode = compiled bytecode (`saltedCreate` create2 address, G22) | OOS (deferred, gas-like) | source-canonical initCode |
| `smtCheckerTests`, `optimizer`, `experimental` pipeline | OOS | not this project's concern |
| Pure parser (`parsing`, `comments`, `unterminatedBlocks`, `license`) and isoltest harness | OOS | solc validates before AST import |

---

*Every one of the 68 semanticTests and 71 syntaxTests categories is represented
above so a reader can confirm nothing was skipped. Net result: the sweep found
**one new wrong-value soundness gap (G1 — user-defined operators run as builtins)**
that both prior reviews missed; a cluster of acceptance over-accepts led by **G2**
(`msg.value` in view), **G3** (`==` on reference types) and **G4** (constant OOB
index), all unreachable on a solc-validated corpus; two completeness over-rejects
(**G14, G13**); and several untested-but-modeled paths (**G17–G22**). The most
suspicious remaining value path from the prior review — S2 calldata element
cleanup — was read to the bottom and confirmed faithful.*
