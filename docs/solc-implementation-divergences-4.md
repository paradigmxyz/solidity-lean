# Implementation-level solc-vs-Solidus divergence review (round 4)

**Fourth implementation-level pass.** Rounds 1–3
(`docs/solc-implementation-divergences.md`, `-2.md`, `-3.md`) read the arithmetic
/ cleanup / conversion / ABI codec / storage-helper families and the analysis-pass
bodies (`ViewPureChecker`, `OverrideChecker`, `ControlFlowAnalyzer`,
`ContractLevelChecker`, `ImmutableValidator`, `DeclarationTypeChecker`) at the
emitted-Yul / rule level and found **no wrong-VALUE divergence** — only
accept/reject-boundary items (E1/E2/O1/CF1-3/PT1, CL1/PK1). This round covers the
families round 3 explicitly left **still-not-reached**, plus fresh acceptance
angles:

1. **`using`-for legality (exhaustive)** — file-level vs contract-level, `global`
   requirement, operator bindings (which operators, function signature
   requirements, duplicate bindings), library vs `{f,g}` vs `*`. solc
   `TypeChecker::endVisit(UsingForDirective)`.
2. **`FunctionCallOptions` legality** — `{value:, gas:, salt:}` allowed-name,
   duplicate-option, payable-value, salt-only-with-`new`, gas-not-with-`new`,
   value-not-for-delegatecall/staticcall. solc
   `TypeChecker::visit(FunctionCallOptions)`.
3. **Struct/nested ABI encode+decode at the byte level** (`ABIFunctions.cpp`
   `abiDecodingFunctionStruct` and array/tuple decoders) — head/tail offsets, the
   "tail past end reverts" bounds checks, per-element fuel — vs Solidus
   `ABI.lean` decode.
4. **Event / error parameter rules** — indexed count ≤ 3 (≤ 4 anonymous),
   indexed reference types, mapping-typed params, reserved `Error`/`Panic`
   redefinition; **`abi.decode` return-type-list arity**.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `6f5ad5e`. Canonical semantics
files are `SolidCore/Solidity/*.lean` (all line numbers below are in that
directory). Nothing was built or run for Solidus; a handful of tiny
**accept/reject** probes used the pinned `solc 0.8.35` binary
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`). Findings are
**CONFIRMED** (both sides read to the rule, usually + probe) or **INFERRED**
(deduced, wants a probe).

---

## Executive summary

**Families / passes actually read (code, not tests), both sides:**

- `TypeChecker::endVisit(UsingForDirective)` (`TypeChecker.cpp:3995-4270`, whole
  body incl. operator-binding sub-block) ↔ Solidus `UsingDecl.checkCore` /
  `checkFileLevel` / `checkContractLevel` / `UsingFunction.check` /
  `FunctionSig.matchesUserDefinedOperatorDecl` / `CheckEnv.resolveUsingBinary
  /UnaryOperator?` (`TypeCheck.lean:12070-12112, 12002-12060, 3827-3846,
  4014-4032`).
- `TypeChecker::visit(FunctionCallOptions)` (`TypeChecker.cpp:2884-3035`, whole
  body) ↔ Solidus's four `Expr.callWithOptions` arms (`new`, ident/function
  pointer, member, generic) + `requireCallOptionsAllowedNames` /
  `requireValueOptionAllowed` / `ensureUniqueNames "call option"`
  (`TypeCheck.lean:6488-6821, 4095-4203`).
- `ABIFunctions.cpp` `abiDecodingFunctionStruct` / `abiDecodingFunctionArray`
  (+ `AvailableLength` bounds checks) ↔ Solidus `ABI.lean`
  `decodeValueAtWithFuel?` / `decodeArgs?` / `Ty.abiDecodeFuel`
  (`ABI.lean:141-149, 319-457`).
- `TypeChecker` event/error visit (`TypeChecker.cpp:695-701` indexed count) ↔
  Solidus `EventDecl.check` / `EventParam.check` / `ErrorDecl.check`
  (`TypeCheck.lean:11847-11917`).

**Headline: NO new wrong-VALUE / wrong-ORDER soundness divergence.** Consistent
with rounds 1–3, every value-producing path stayed faithful. The `using`-for
directive was the richest unreviewed surface and it yields **one new live
COMPLETENESS over-reject (UF1)** plus two niche importer-masked over-accepts
(UF2/UF3). `FunctionCallOptions`, the struct/nested ABI decoder, and the
event/error/`abi.decode` acceptance rules are **faithful** (earned negatives).

**Ranked NEW findings**

| # | Area | Direction | Severity | Confidence |
|---|------|-----------|----------|------------|
| **UF1** | file-level `using … for T global;` where `T` is a **struct / enum / contract** (any user-defined type that is not a UDVT) | **over-reject** (Solidus rejects; solc accepts) | COMPLETENESS — **live differential edge, common real-world pattern** | CONFIRMED |
| UF2 | operator binding `using {f as +} for T global;` where `f`'s params are **not both `T`** (e.g. `f(T, uint)`) | over-accept at decl (Solidus accepts binding; solc errors 1884) | acceptance-boundary wrong-accept — importer-masked, binding is dead at use | CONFIRMED |
| UF3 | **duplicate** operator binding for the same operator+type never used | over-accept (Solidus errors only at use; solc errors 4705 at decl) | acceptance-boundary wrong-accept — importer-masked | INFERRED |

**UF1 is the only NEW finding with a live differential edge, and it is the
highest-impact acceptance divergence found in any round so far**: `using L for S
global;` / `using {f} for S global;` on a struct is an *extremely common*
real-world library idiom (a file-level library attached globally to a struct
type). solc accepts it; Solidus rejects it on import because its file-level
`global` rule only admits UDVT targets. UF2/UF3 are the same importer-masked
over-accept class as round-3's CL1 (solc rejects the program → no AST is exported
→ Solidus never sees it in the differential harness).

**No new soundness (wrong-value) divergence** — earned negative for the
`using`-for value semantics, `FunctionCallOptions`, the struct/nested ABI codec,
and the event/error/`abi.decode` acceptance surfaces.

---

## 1. NEW findings

### UF1 — `using … for T global;` on a non-UDVT user-defined type — over-reject — CONFIRMED — NEW

- **solc** `TypeChecker.cpp:3997-4021` (`endVisit(UsingForDirective)`): the only
  constraint the `global` keyword imposes is that the directive is at file level
  (`!m_currentContract`), names a type, and the type has a `typeDefinition()`
  (i.e. is a *user-defined type* — struct, enum, UDVT, **or** contract) defined
  in the same source unit. `4117_error` fires only if the type is defined in a
  *different* source unit; `8841_error` ("Can only use \"global\" with
  user-defined types") fires only for built-in / elementary types. A **struct**,
  **enum**, or **contract** defined in the same file is a fully legal `global`
  target — both the library form (`using L for S global;`) and the brace form
  (`using {f} for S global;`).
- **Solidus** `UsingDecl.checkFileLevel` (`TypeCheck.lean:12095-12112`): when
  `decl.global`, it requires the target to be `Solidity.Ty.user path` **and**
  `env.types.isUserValueTypePath path`. `isUserValueTypePath`
  (`TypeCheck.lean:160-163`) returns true **only for UDVTs** (it delegates to
  `lookupUserValueType?`). So any `global` directive whose target is a struct,
  enum, or contract is rejected with
  `invalidContractHeader "global using directive target is not a user value
  type"`. This UDVT-only gate is correct for *operator* bindings
  (`UsingFunction.check:12024-12032`, matching solc's 5332) but is wrongly
  applied to *all* file-level `global` directives.
- **Consequence:** both of the following, **accepted by solc, are rejected by
  Solidus**:

  ```solidity
  struct S { uint x; }
  function f(S memory s) pure returns (uint) { return s.x; }
  using {f} for S global;               // solc: OK    Solidus: rejected
  ```
  ```solidity
  library L { function f(S storage s) internal view returns (uint) { return s.x; } }
  struct S { uint x; }
  using L for S global;                 // solc: OK    Solidus: rejected
  ```

  Both probes compiled cleanly under the pinned `solc 0.8.35`. The importer
  imports file-level using directives and carries the `global` flag
  (`scripts/solc_ast_to_lean_source.py:1876-1885, 2011-2012`;
  `SOURCE_SCALAR_FIELDS` includes `('UsingForDirective','global')`), and
  `checkSourceUsingDecls` wires `checkFileLevel` at file scope
  (`TypeCheck.lean:13413-13417`). This is therefore a **live differential edge**:
  solc emits an AST, Solidus rejects it on import. Over-reject → COMPLETENESS,
  sound-preserving, but this is the highest-impact acceptance divergence surfaced
  in rounds 1–4 because global-`using`-for-struct is a mainstream library idiom.
  A fix narrows the `global` file-level gate to "target is any user-defined type
  defined in this source unit" (struct/enum/UDVT/contract), keeping the
  UDVT-only restriction for *operator* bindings only.

### UF2 — operator binding whose function params are not both the target type — over-accept (masked) — CONFIRMED — NEW

- **solc** `TypeChecker.cpp:4158-4186` (`1884_error`): for a binary operator
  binding, solc requires `parameterCount == 2`, `identicalFirstTwoParameters`
  (`*parameterTypes[0] == *parameterTypes[1]`), **and**
  `firstParameterMatchesUsingFor` (`*usingForType == *parameterTypes.front()`) —
  i.e. **both** parameters must be exactly the target UDVT. `f(T, uint)` or
  `f(uint, T)` is rejected (1884). (Unary: exactly one parameter of type `T`.)
- **Solidus** `FunctionSig.matchesUserDefinedOperatorDecl`
  (`TypeCheck.lean:3827-3846`), used at the declaration check
  (`UsingFunction.check:12036-12041`), requires only `sig.params.length == 2`
  (binary), `sig.mutability == pure`, `sig.returns == [resultTy]`, and
  `FunctionSig.hasParamTy targetTy sig.params` — the latter is satisfied if the
  target type appears in **at least one** parameter position
  (`hasParamTy:3799-3801`), not both. So `function addMixed(T a, uint256 b) pure
  returns (T)` bound as `+` **passes** the declaration check.
- **Consequence:** `type T is uint256; function addMixed(T,uint256) pure returns
  (T); using {addMixed as +} for T global;` is **accepted at the binding site by
  Solidus, rejected by solc (1884)** (probe confirmed solc rejects). The binding
  is *dead*: at a use `x + y` (both `T`), the call-site matcher
  `matchesUserDefinedBinaryOperator` (`:3803-3813`) additionally requires
  `matchesCheckedArgs [(none,lhs),(none,rhs)]` against `params [T, uint256]`, and
  `rhs : T` will not convert to `uint256`, so the operator is never resolved and
  a real `+` on `T` still fails. Since solc rejects the program outright, no AST
  is exported → **importer-masked**; same class/direction as round-3 CL1.

### UF3 — duplicate operator binding for the same operator+type — over-accept (masked) — INFERRED — NEW

- **solc** `TypeChecker.cpp:4229-4254` (`4705_error`): if two visible bindings
  define the same operator for the same operand type
  (`matchingDefinitions.size() >= 2`), it is an error *at the directive*.
- **Solidus** detects a duplicate operator binding only lazily, at a **use
  site**: `CheckEnv.resolveUsingBinaryOperator?` / `…UnaryOperator?`
  (`TypeCheck.lean:4014-4032`) return `TypeError.ambiguousFunction "operator"`
  when more than one candidate matches, but there is no directive-level
  duplicate-binding check in `UsingDecl.checkCore`/`checkFileLevel`.
- **Consequence:** a program that binds the same operator twice for one type but
  **never uses** it is accepted by Solidus and rejected by solc (4705). When the
  operator *is* used both reject (Solidus via `ambiguousFunction`), so the window
  is exactly "duplicate binding, operator never applied". solc rejects at the
  directive → **importer-masked**. INFERRED (the use-site path is read; the
  never-used over-accept is deduced), low priority.

---

## 2. `using`-for — otherwise faithful (rule-by-rule)

All CONFIRMED SUPPORTED except UF1–UF3 above:

| solc rule (`TypeChecker.cpp` / resolver) | error | Solidus |
|---|---|---|
| brace-list free-function must exist / library-member must exist | (name res) | `UsingFunction.check` candidate filter, `!candidates.isEmpty` (`:12041,12060`) |
| library-form target must be a library | (name res) | `checkCore` `libraryDecl.kind == library` (`:12077-12078`) |
| attached function needs ≥1 parameter (first-arg bind) | 4731 | `matchesCheckedArgs`/member-candidate machinery requires a bindable self param (`usingMemberCandidate?:3606`); a zero-param free fn produces no candidate |
| private library fn cannot attach outside its library | 6772 | `FunctionSigs.nonPrivate` filter on candidates (`:12046,12056`) |
| operator binding only in `global` directive | 3320 | `require global` (`:12011-12013`) |
| operator only pure free function | 7775 | `matchesUserDefinedOperatorDecl` requires `mutability == pure` (`:3834,3842`) + `libraryPath.segments.isEmpty` (free) (`:12014-12016`) |
| operators only for UDVTs | 5332 | `require isUserValueTypePath` on operator target (`:12024-12032`) |
| operator param-shape (both params `T`, count 1/2) | 1884 | partial — **UF2 over-accept** (`hasParamTy` vs both-params) |
| operator return-type (`T`, or `bool` for compare/`!`) | 7743 | `returns == [resultTy]` with `userDefinedResultTy?` computing bool for compare ops (`:3792-3797`) |
| duplicate operator binding | 4705 | use-site `ambiguousFunction` only — **UF3 masked over-accept** |
| `global` only at file level | (8841/contract guard) | `checkContractLevel` `require (!decl.global)` (`:12091-12093`) |
| target type must be valid / not a library type | (type res) | `checkCore` `checkTy` + `!containsLibraryType` (`:12082-12086`) |
| `global` target must be a same-file user-defined type | 8841/4117 | **UF1 over-reject** (UDVT-only instead of any user-defined type) |

`using … for *` (wildcard) value semantics are the in-flight G20 arc
(`docs/DECISIONS.md`); the wildcard has no extra file-level `global` legality
rule beyond the above, so UF1 applies to `for *` only through its (elementary)
targets, which are already correctly barred from `global` by solc's 8841.

---

## 3. `FunctionCallOptions` — FAITHFUL (no divergence)

solc `TypeChecker::visit(FunctionCallOptions)` (`TypeChecker.cpp:2884-3035`) and
Solidus's four `Expr.callWithOptions` arms (`TypeCheck.lean:6488-6821`) agree
rule-for-rule:

| solc rule | error | Solidus |
|---|---|---|
| options only on external call / creation | 2193 | only the `new`, member-external, function-pointer, and low-level arms accept options; other call shapes have no options arm |
| duplicate option name | 9886 | `ensureUniqueNames "call option" (CallOptions.names options)` at every arm (`:6491,6578,6672,6773`) |
| `salt` only with `new`; expects `bytes32` | 2721 | only the `new` arm allows `salt` (`requireCallOptionsAllowedNames ["value","salt"]:6493`); other arms omit `salt` |
| `gas` cannot be used with `new` | 9903 | `new` arm's allow-list is `["value","salt"]` — `gas` rejected |
| `value` requires payable fn / ctor | 7006 | `requireValueOptionAllowed sig.mutability options` (`:6573,6624,6761,6820`, def `:4195-4203`) |
| `value` not for `delegatecall` | 6189 | `delegatecall`/`staticcall` low-level allow-list is `["gas"]` only (`:6687-6688`) |
| `value` not for `staticcall` | 2842 | same `["gas"]` allow-list |
| `value`/`gas` expect `uint256` | (expectType) | value/gas args checked assignable to `uint256` (`:6713,6725` and option-loop) |
| unknown option name | 9318 | `requireCallOptionsAllowedNames` rejects any name outside the allow-list (`:4095-4108`) |

The one un-probed corner is solc's `1645_error` ("options already set, combine
into a single `{...}`") for a **chained** `f{value:1}{gas:2}()`. Its
reachability depends on how the importer nests a double `FunctionCallOptions`
node; solc rejects it, so if the importer does not synthesize a nested
`callWithOptions` this is importer-masked. Marked UNTESTED — not a value
divergence either way.

---

## 4. Struct / nested ABI decode — FAITHFUL (bounds + fuel sound)

solc's `abiDecodingFunctionStruct` / `abiDecodingFunctionArray(AvailableLength)`
allocate a fresh memory object per struct/array and revert on an out-of-bounds
head or tail (`offset < dataEnd`, `offset + length*stride <= dataEnd`). Solidus's
`ABI.lean` decoder reproduces the observable:

- **Bounds ("tail past end reverts").** Every read goes through `readWord?` /
  `readBytes?` (`ABI.lean:18-24, 63-66`), which return `none` when the slice
  runs past the input. A `none` at any depth propagates up the `do`-blocks in
  `decodeValueAtWithFuel?` (`:319-427`) → `decodeArgs?` (`:442-444`) → the
  `abi.decode` / calldata-decode call fails, i.e. **reverts**. So a dynamic head
  pointing past the end, or a length word implying a tail past the end, decodes
  to `none` (revert) — matching solc's explicit bounds `revert`. CONFIRMED.
- **Head/tail offset discipline.** Dynamic array (`:373-388`) reads the offset
  word, then the length at that offset, then elements from `offset + wordBytes`
  with per-element stride `Ty.abiHeadWords? elementTy`; fixed-array-of-dynamic
  and tuple/struct-with-dynamic (`:389-424`) read a relative offset first and
  decode the sub-object from `argData.drop offset`. This is the same
  head-is-relative-to-enclosing-object rule verified for the *encode* side in
  round 2 §2, run in reverse. CONFIRMED.
- **Fuel is exactly deep enough (no fuel-exhaustion over-reject).**
  `Ty.abiDecodeFuel` (`:141-149`) is `depth+1`: `dynamicArray e → fuel(e)+1`,
  `tuple es → Σ fuel + 1`. When decoding an array/tuple, each element is decoded
  with the *decremented* fuel (`fuel`, not `fuel+1`), which equals
  `abiDecodeFuel(elementTy)` — enough for arbitrarily *wide* structures (fuel
  counts nesting depth, not element count). So a struct with dynamic members,
  nested structs, and struct arrays decodes without spurious `none`. CONFIRMED.
- **Per-slot validation.** `bool` must be 0/1, `address` must fit 160 bits,
  `bytesN`/external-function padding must be zero, else `none` (revert) — matches
  solc's `validator` calls emitted by the struct decoder. (`:321-367`.)

The Yul *allocation sequence* (free-memory-pointer bump order) is not
independently reachable from Solidus's value-level interpreter and remains
observably-confirmed only (rounds 1–2); no value or revert divergence exists.

---

## 5. Event / error / `abi.decode` acceptance — FAITHFUL

| solc rule | error | Solidus |
|---|---|---|
| > 3 indexed args (non-anonymous event) | 7249 | `EventDecl.check` `indexedCount <= 3` (`indexedLimit:11857-11859`, check `:11885-11888`) |
| > 4 indexed args (anonymous event) | 8598 | `indexedLimit` returns 4 when `event.anonymous` |
| indexed **reference** types allowed (hashed) | (accepted) | `EventParam.check` requires only ABI-encodable + not-mapping (`:11861-11870`); reference types pass |
| mapping-typed event/error param rejected | (type) | `!Ty.containsMapping` in `EventParam.check`/`checkErrorParam` (`:11869,11899`) |
| cannot redefine built-in `Error` / `Panic` | (reserved) | `ErrorDecl.check` `require (!(name == "Error" \|\| name == "Panic"))` (`:11912-11914`); probe: solc rejects `error Error(uint)`, Solidus rejects too |
| `abi.decode(data, (T, …))` needs ≥1 target type, exactly 2 args | (arity) | `member == "decode"` arm requires exactly 2 args + `tys.length > 0` (`:6205-6222`) |

All CONFIRMED SUPPORTED.

---

## 6. Families reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] `using`-for **legality** full: file-level/contract-level `global` gate,
  library vs brace-list, operator bindings (which ops, pure-free, UDVT-only,
  param/return shape, duplicates) — **UF1 over-reject** (global on
  struct/enum/contract), **UF2/UF3 masked over-accepts** (operator param-shape,
  duplicate binding); everything else SUPPORTED
- [x] `FunctionCallOptions` legality full (allowed names, duplicate, payable
  value, salt-only-`new`, gas-not-`new`, value-not-delegate/static) — SUPPORTED;
  chained-`{...}{...}` (1645) UNTESTED/likely-masked
- [x] Struct / nested ABI **decode** byte-level: bounds ("tail past end
  reverts"), head/tail offsets, fuel sufficiency, per-slot validation — FAITHFUL
- [x] Event indexed-count (7249/8598) + indexed reference types + mapping-param
  rejection — SUPPORTED
- [x] Error param rules + reserved `Error`/`Panic` redefinition + `abi.decode`
  arity / type-list — SUPPORTED

**Still NOT reached (worklist for a future pass):**

- `abiDecodingFunctionStruct` free-memory-pointer / allocation *sequence* at the
  emitted-Yul level — not independently reachable from Solidus's value-level
  interpreter (observable confirmed rounds 1–2 + this round; the Yul bump order
  itself is out of scope for a value semantics).
- Chained `f{value:}{gas:}()` (solc 1645) — resolve whether the importer
  synthesizes a nested `callWithOptions`; if not, importer-masked.
- `checkStorageLayoutSpecifier` (7587/8894) and `checkStorageSize`
  (7676/5026 too-much-storage) — storage-layout *specifier* keyword and the
  256-slot-overflow acceptance rule; a probe would confirm parity (value level is
  faithful).
- Denomination / scientific / rational literal edge cases and `\x`/`\u` escape +
  address-checksum validation — performed by solc **before** AST export
  (importer-masked); not independently modeled by Solidus.
- `ControlFlowRevertPruner` full algorithm (CF2 residuals) — IN-FLIGHT sibling
  arc, not re-examined.

---

## 7. Bottom line

Reading the previously-unreached acceptance surfaces — the full `using`-for
directive legality (file/contract `global` gate, library vs brace vs operator
bindings, operator signature rules and duplicates), the full `FunctionCallOptions`
option rules, the struct/nested ABI **decoder** at the byte level, and the
event/error/`abi.decode` acceptance rules — surfaced **no new wrong-value or
wrong-order soundness divergence**, matching rounds 1–3. `FunctionCallOptions`,
the struct/nested ABI codec (bounds, head/tail, fuel, per-slot validation), and
the event/error/`abi.decode` acceptance rules are **faithful** (earned
negatives).

The one NEW live divergence is **UF1**, and it is the highest-impact acceptance
edge found across all four rounds: Solidus rejects `using L for S global;` /
`using {f} for S global;` on a struct (or enum/contract) — a mainstream
real-world library idiom — because its file-level `global` gate admits only UDVT
targets, whereas solc admits any same-file user-defined type. It is an
over-reject (COMPLETENESS, sound-preserving) but with a live differential edge on
natural code. **UF2/UF3** are niche, importer-masked over-accepts in the
operator-binding validation (wrong param shape; duplicate binding never used),
the same class as round-3's CL1. No computed value changes in any finding.
