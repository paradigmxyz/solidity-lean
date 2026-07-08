# Implementation-level solc-vs-Solidus divergence review (round 3)

**Third implementation-level pass.** Rounds 1 and 2
(`docs/solc-implementation-divergences.md`, `-2.md`) read the arithmetic /
cleanup / conversion / ABI codec / storage-helper families and the analysis-pass
bodies (`ViewPureChecker`, `OverrideChecker`, `ControlFlowAnalyzer`) at the
emitted-Yul / rule level and found **no wrong-VALUE divergence** — only
accept/reject-boundary items (E1/E2/O1/CF1-3/PT1/AE1). This round covers the
families round 2 explicitly left **still-not-reached**:

1. `ContractLevelChecker.cpp` — receive/fallback signature rules, base-constructor
   argument rules (arity / given-twice / abstract-if-missing), duplicate/illegal
   definitions, name-clash rules, interface and library requirements.
2. `ImmutableValidator.cpp` (full) — assigned-exactly-once / constructor-only /
   read-before-write.
3. Full `abi.encodePacked` validation predicate + `abiDecodingFunctionStruct`.
4. `DeclarationTypeChecker.cpp` — type-name resolution, recursive-struct
   detection, array-length rules, mapping-key restrictions, enum size, UDVT.
5. Adjacent control-flow (unreachable-after-return); `TypeChecker`
   overload-resolution ambiguity; `new`-contract creation type rules;
   self-referential `constant`.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `2db94a7`. Canonical semantics
files are `SolidCore/Solidity/*.lean` (`TypeCheck.lean` is 13 399 lines; all line
numbers below are in that directory). Nothing was built or run for Solidus; a
few tiny **accept/reject** probes used a local `solc 0.8.26` (the rules probed
are byte-identical in the 0.8.35 source read here). Findings are **CONFIRMED**
(both sides read to the rule, often + probe) or **INFERRED** (wants a probe).

---

## Executive summary

**Families / passes actually read (code, not tests), both sides:**

- `ContractLevelChecker.cpp` (whole body) ↔ Solidus `ContractDecl.check` /
  `ContractDecl.checkKindShape` / `checkBaseConstructorArgsForDeployment` /
  `ModifierInvocation.check{,BaseConstructor}` / the receive/fallback signature
  arm of `checkFunctionHeader` (`TypeCheck.lean`).
- `ImmutableValidator.cpp` (whole body) ↔ Solidus immutable-lvalue gating +
  the interpreter's default-zero immutable model.
- `DeclarationTypeChecker.cpp` (struct recursion, array length, mapping key, enum
  size, UDVT, address kind) ↔ Solidus `Ty.isValid` / `Ty.isMappingKeyShape` /
  `Ty.hasForbiddenStructReferenceCycle` / `EnumDecl.check` /
  `UserValueTypeDecl.check`.
- `TypeChecker.cpp` `abi.encodePacked` validation (`typeSupportedByOldABIEncoder`)
  ↔ Solidus `Ty.isAbiEncodePackedArgShape` / `isAbiEncodePackedArrayElementShape`.
- `TypeChecker.cpp` overload resolution (argument-dependent lookup) ↔ Solidus
  `resolveChecked` / `matchesCheckedArgs` / `canAssignToIn` /
  `requiresExactLiteralFit`.
- `new`-expression contract-creation type rules ↔ `requireCreatableContractDecl`.

**Headline: NO new wrong-VALUE / wrong-ORDER soundness divergence.** Consistent
with rounds 1-2, every value-producing path stayed faithful; the two NEW
divergences are acceptance-boundary. Two round-2 INFERRED items are now closed
(AE1 is a non-divergence; PT1 is fixed), and the biggest round-2 worry — the
immutable "exactly-once" invariant — is **cleared**: solc's IR pipeline defaults
an unassigned immutable to `0` and allows multiple assignments (last write wins),
so there is no frontend exactly-once rule for Solidus to miss.

**Ranked NEW findings**

| # | Area | Direction | Severity | Confidence |
|---|------|-----------|----------|------------|
| **CL1** | base-ctor: bare modifier-style base-constructor call (no arg list) on a **zero-param** base | **over-accept** (Solidus accepts; solc errors 1563) | acceptance-boundary wrong-accept — niche, importer-masked | FIXED (2026-07-08) |
| **PK1** | `abi.encodePacked` of a **nested array** (`uint[2][3]`, array-of-array element) | **over-reject** (Solidus rejects; solc accepts) | COMPLETENESS — live differential edge | FIXED (2026-07-08) |

**PK1 is the only NEW finding with a live differential edge**: solc accepts
`abi.encodePacked(uint[2][3])`, so the importer produces an AST and Solidus then
rejects it — a real "Solidus fails to compile a valid program" divergence. CL1
is an over-accept of the standalone acceptance oracle (same class as round-2's
E1/O1) but is masked in the differential harness because solc rejects the program
before an AST is ever exported, and the triggering syntax (a base written as a
bare `Base` modifier with no parentheses, base constructor taking zero
parameters) is unnatural.

**No new soundness (wrong-value) divergence** — earned negative for the
declaration/contract-level acceptance surfaces, the encodePacked/decode codec,
and overload resolution.

---

## 1. NEW findings

### CL1 — bare modifier-style base-constructor call on a zero-param base — over-accept — CONFIRMED — FIXED (2026-07-08)

> **FIXED (2026-07-08, `gap/round3-pk1-cl1`).** `ModifierInvocation` now carries
> `hasArgList : Bool := true` (`Ast.lean`); the importer sets it from solc's
> `arguments == null` vs `[]` (`solc_ast_to_lean_source.py`); and
> `ModifierInvocation.check` rejects a base-constructor modifier with
> `hasArgList = false` (`TypeCheck.lean`, "modifier-style base constructor call
> without arguments"). Matches solc: bare `Base` rejected regardless of base
> constructor params; `Base()` and inheritance-list `Base(args)` accepted.
> Witnesses `bareModifierBaseConstructorRejected` / `parenModifierBaseConstructorAccepted`;
> solc-reject fixture `invalid/BareModifierBaseConstructor.sol`.


- **solc** `ContractLevelChecker.cpp:359-383` (`checkBaseConstructorArguments`):
  for every modifier on a constructor that resolves to a base contract, if the
  modifier has **no argument list** (`!modifier->arguments()`, i.e. bare `Base`
  written where parentheses are absent) it is **always** an error —
  `1563_error` "Modifier-style base constructor call without arguments." — even
  when the base constructor takes zero parameters. `Base()` (empty parens) is
  accepted; bare `Base` is not.
- **Solidus** cannot see the distinction. `ModifierInvocation` carries only
  `args : List Arg := []` (`Ast.lean:302-305`) with no "arguments present" flag,
  and the importer collapses solc's `arguments == null` into `[]`
  (`scripts/solc_ast_to_lean_source.py:1412-1413`). `ModifierInvocation.check`
  (`TypeCheck.lean:10532-10543`) routes a base-constructor modifier to
  `checkBaseConstructor` (`:10503-10530`), which type-checks the (empty) argument
  list against the base constructor signature. For a **zero-parameter** base
  constructor, arity `0 == 0` succeeds → **accepted**.
- **Consequence:** `contract A { constructor() {} } contract B is A {
  constructor() A {} }` is **accepted by Solidus, rejected by solc (1563)**
  (probe confirmed: solc rejects bare `A`, accepts `A()`). When the base
  constructor has ≥ 1 parameter, Solidus's arity check rejects the bare form too
  (coincidentally matching solc, though via arity rather than 1563), so the
  over-accept window is exactly: **bare base modifier + zero-parameter base
  constructor**. Acceptance-boundary wrong-accept; masked in the differential
  harness (solc emits no AST for a rejected program) and syntactically unusual.
  Same class and direction as round-2 E1/O1.

### PK1 — `abi.encodePacked` of a nested array — over-reject — CONFIRMED — FIXED (2026-07-08)

> **FIXED (2026-07-08, `gap/round3-pk1-cl1`).** Two edits: (1)
> `Ty.isAbiEncodePackedArrayElementShape` (`TypeCheck.lean`) gained a
> `Ty.array element size` case that accepts a nested array iff its inner
> dimension is **static** (`some _`) and recurses on the element — matching
> `typeSupportedByOldABIEncoder` (reject only a dynamically-sized *base* array).
> (2) The interpreter's `abiEncodePackedArrayElement?` (`Interpreter.lean`) now
> recurses into a `fixedArray` element, padding each innermost value to a 32-byte
> word in-place. Probe-confirmed boundary: `uint[2][3]`, `uint[2][]`,
> `uint[2][2][2]` ACCEPT; `uint[][3]`, `uint[2][][2]`, `bytes[]`, `string[]`
> REJECT (9578). Forge lane `packed-nested-static-array` pins the 128-byte padded
> layout against solc's own `abi.encodePacked`; Lean value witnesses
> `abiEncodePackedNestedStaticArrayValueMatches` /
> `abiEncodePackedDynamicOuterStaticInnerValueMatches` pin the same bytes;
> `invalid/PackedDynamicInnerArray.sol` guards against over-accepting a dynamic
> inner dimension.


- **solc** `TypeChecker.cpp:2167-2174` rejects a packed-encoding argument only
  when `!typeSupportedByOldABIEncoder(*argType, false)` (`9578_error` "Type not
  supported in packed mode."). `typeSupportedByOldABIEncoder`
  (`TypeChecker.cpp:55-70`) rejects **structs** and any **array whose base is a
  dynamically-sized array** (so `bytes[]`, `string[]`, `uint[][]` are rejected),
  but **accepts a nested array of value types with a static inner dimension** —
  e.g. `uint[2][3]`, whose inner `uint[2]` is a static (non-dynamic) array — and
  recurses to the value base. Probe: solc **compiles**
  `abi.encodePacked(uint[2][3] memory a)`.
- **Solidus** `Ty.isAbiEncodePackedArgShape` (`TypeCheck.lean:4217-4242`) delegates
  an array argument to `Ty.isAbiEncodePackedArrayElementShape`
  (`:4244-4265`), whose element cases cover only value types, contract, enum,
  UDVT, and external function — there is **no `Ty.array` case**, so a nested-array
  element falls to `_ + 1, _ => false`. Thus `uint[2][3]` (element `uint[2]` is an
  array) is **rejected** by Solidus's `checkAbiEncodePackedArgs`
  (`:4291-4296`, wired at `:6191-6192`).
- **Consequence:** `function f(uint[2][3] memory a) pure returns (bytes memory)
  { return abi.encodePacked(a); }` is **rejected by Solidus, accepted by solc**.
  This is a live differential edge (solc produces an AST; Solidus rejects on
  import). Over-reject → COMPLETENESS, sound-preserving. Note a full fix would
  also need the interpreter's packed encoder, which today rejects
  `fixedArray`/`dynamicArray`/`tuple` elements
  (`Interpreter.lean` `abiEncodePackedArrayElement?`, round-2 §2) to learn to pad
  nested-array elements to 32 bytes.

---

## 2. Round-2 INFERRED items now CLOSED

### AE1 (round-2) — RESOLVED: non-divergence

Round 2 left open whether Solidus rejects `bytes[]` / `string[]` /
array-of-dynamic elements in `abi.encodePacked` (a potential over-accept /
wrong-bytes in the interpreter fall-through). It **does**:
`isAbiEncodePackedArrayElementShape` (`TypeCheck.lean:4244-4265`) allows only
value / contract / enum / UDVT / external-fn elements and rejects `bytes`,
`string`, nested arrays, tuples, and structs, so the interpreter's right-pad
fall-through is unreachable. Probe: solc rejects `bytes[]` (9578) and Solidus's
predicate rejects it too. `uint[]` (dynamic array of a value type) is accepted by
both. AE1 is not a divergence. (The residual boundary is PK1 above, the opposite
direction.)

### PT1 (round-2) — FIXED

Round 2 could not find a `constant`-value cycle detector and marked PT1
(self/mutually-cyclic `constant` → solc 6161) INFERRED-over-accept. It now
exists: `ContractDecl.check` runs
`require (!StateVarDecls.constantsHaveCycle (stateVars ++ sourceConstants))`
(`TypeCheck.lean:12354-12355`). Not a divergence. (Consistent with the
`ce810e1` "reject cyclic constants" fix.)

---

## 3. ImmutableValidator — the "exactly-once" worry is CLEARED

`ImmutableValidator.cpp` (whole file, `:26-68`) enforces **exactly one** rule:
`1581_error` "Cannot write to immutable here" for any write to an immutable state
variable outside inline-init or the constructor. Solidus matches — an immutable
identifier is an lvalue only when `env.inConstructor`
(`TypeCheck.lean:5153`, ident case).

The round-2 worklist asked whether solc's "assigned **exactly once**, not in a
loop/branch, not read before write" is enforced and whether Solidus over-accepts.
Reading the whole path and probing solc **clears this**:

- There is **no frontend exactly-once rule.** The only related string,
  `"Leftover immutables."` (`CompilerStack.cpp:1513`), is a codegen `solAssert`,
  and the legacy-pipeline `CodeGenerationError 1284` ("Some immutables were read
  from but never assigned") fires only under `bytecodeFormat: legacy` +
  `optimize-yul` (see `test/.../immutable/no_assignments.sol`).
- Under the default **via-IR** pipeline, solc **compiles** all of: an immutable
  that is never assigned but read (`uint immutable x; f() returns x;` — reads
  `0`), a **doubly-assigned** immutable (`x=1; x=2;` — last write wins), and one
  assigned only in `if(false)` / inside a loop. Probes confirmed each compiles.
- Solidus's model matches: writes gated to the constructor, an unwritten
  immutable reads its type default (`0`), and repeated constructor writes take the
  last value. No over-accept, no wrong value. (solc also performs **no**
  read-before-write ordering analysis for immutables — `read_in_function_before_init.sol`
  compiles — so Solidus need not either.)

**Verdict: SUPPORTED / non-divergent (CONFIRMED).**

---

## 4. ContractLevelChecker — thoroughly covered (CL1 is the only gap)

Rule-by-rule correspondence read on both sides (all CONFIRMED SUPPORTED except
CL1):

| solc rule (ContractLevelChecker.cpp) | error | Solidus |
|---|---|---|
| receive must be payable / external / no-params / no-returns | 7793/4095/6899/6857 (`:203-228`) | receive arm `TypeCheck.lean:10372-10386` |
| library cannot have receive | 4549 (`:210-211`) | `anyConstructorLike` incl. receive/fallback `:12327-12329` |
| ≤1 constructor / fallback / receive | 7997/7301/4046 (`:148-188`) | `:12389-12397` |
| duplicate function (same name+extern params) | 1686 (`findDuplicateDefinitions :232-290`) | `ensureNoDuplicateSignatures` `:12384` |
| duplicate event | 5883 (same) | `ensureNoDuplicateAbiSignatures` `:12400` |
| external overload clash after conversion | 9914 (`checkExternalTypeClashes :466-501`) | `ensureNoDuplicateExternalAbiSignatures` `:12385` |
| 4-byte selector hash collision | 1860 (`checkHashCollisions :503-517`) | `ensureNoDuplicateExternalAbiSelectors` `:12387` |
| non-abstract contract with unimplemented member → must be abstract | 3656 (`checkAbstractDefinitions :340-355`) | `checkInheritedAbstractImplemented(Aux)` `:10014-10035,10205-10219` + `checkKindShape :12336-12345` |
| interface cannot be explicitly abstract | 9348 (`:330-331`) | `:12305-12306` |
| library cannot be abstract | 9571 (`:332-333`) | `:12322-12323` |
| **base ctor arguments given twice** (list + modifier, or two modifiers) | 3364 (`:434-462`) | `baseConstructorArgsForDeployment?` → "specified twice" `:12266-12272` (probe: both reject) |
| **no args to a base ctor that needs them** (non-abstract) | 3415 (`:399-419`) | arity check `:12274-12284` (probe: both reject) |
| **bare modifier-style base ctor call w/o arg list** | 1563 (`:378-382`) | **CL1 over-accept** (zero-param base) |
| library may not inherit | 9469 (`:524-525`) | `library has bases` `:12320-12321` |
| library non-constant state var | 9957 (`:527-529`) | `StateVars.allConstant` `:12324-12326` |
| interface: no state vars / no constructor / all-external-decls | (elsewhere) | `checkKindShape :12304-12318` (probe: constant-in-interface rejected both) |

Base-constructor **argument type/arity** checking is real on the Solidus side
(`checkBaseConstructor` `:10503-10530`, `BaseSpecifier.check` `:12211-12237`),
using the same assignable-args machinery as ordinary calls.

---

## 5. DeclarationTypeChecker — covered

| solc rule (DeclarationTypeChecker.cpp / TypeChecker.cpp) | error | Solidus |
|---|---|---|
| recursive struct (self by value, through fixed arrays / nested structs; NOT through dynamic arrays / mappings) | 2046 (`:114-137`, `finalBaseType(true)`) | `Ty.hasForbiddenStructReferenceCycle` `TypeCheck.lean:11765-11808` (recurses `user`, fixed `array (some _)`, `tuple`; stops at dynamic array / mapping), wired `StructField.check :11815` (probe: both reject `struct S{ S a; }`) |
| array length must be integer-constant | 5462 (`:346-351`) | importer requires concrete static length (`scripts/...:558-575`); non-constant never reaches Solidus |
| array length zero | 1406 (`:352-353`) | `Ty.isValid` array `some size` → `size > 0` `:719-720` |
| array length fractional / negative | 3208/3658 (`:354-357`) | length is `Nat` (importer); impossible by representation |
| array length > 2**256-1 | 1847 (`:358-363`) | **not bounded** in `Ty.isValid` (`:719-720`); masked by importer (solc rejects first) — theoretical minor |
| mapping key must be elementary / UDVT / contract / enum | 7804 (`:245-266`) | `Ty.isMappingKeyShape` `:459-473` (rejects struct / array / mapping / tuple / function) via `Ty.isValid` `:721-723` |
| enum > 256 members | 1611 (`:65-72`) | `EnumDecl.check` `decl.cases.length > 0 && <= 256` `:11832` |
| UDVT underlying must be elementary value type | 8657/8129 (`:142-164`) | `UserValueTypeDecl.check` `isBuiltInValueTypeShape` `:11838+` |
| `new` on interface / library / abstract | "Cannot instantiate an interface." / 3656-adjacent (`TypeChecker.cpp`) | `requireCreatableContractDecl` requires `kind == contract && !abstract` `:4693-4700` (probe: both reject `new I()`) |

---

## 6. Overload resolution (argument-dependent lookup) — CONFIRMED non-divergent

This was a suspected over-accept: does Solidus silently pick one overload where
solc reports ambiguity? A checked integer literal gets concrete type `uint256`
(`literalTy? :4058-4064`), which alone would make `f(1)` match only `f(uint256)`
and not `f(uint8)`. But the checked-argument acceptance test special-cases
literals:

- `matchesCheckedArgs` → `checkedExprParamsAccept` → `CheckedExpr.canAssignToIn`
  (`TypeCheck.lean:3105-3110`): when `expr.requiresExactLiteralFit`
  (numeric type + untyped number-literal source, `:3092-3094`, `:1355-1366`) it
  uses `implicitLiteralFits expected expr.source` (`:1329+`) **instead of** the
  concrete-type conversion.
- So for `f(1)` with overloads `f(uint8)` / `f(uint256)`, the literal fits both
  → `resolveCheckedLoop` sees two distinct resolution targets →
  `TypeError.ambiguousFunction` (`:3489`). Probe: solc rejects the same program
  ("No unique declaration found after argument-dependent lookup"). **Match.**
- `f(300)` fits only `uint256` → both sides resolve `f(uint256)` uniquely.
  **Match.**

Overload resolution over literals is faithful. (CONFIRMED)

---

## 7. Families reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] `ImmutableValidator` full — write-location (1581) SUPPORTED; exactly-once /
  read-before-write **cleared** (solc has no frontend rule; defaults to 0, allows
  double-assign)
- [x] `ContractLevelChecker` receive/fallback signature (7793/4095/6899/6857/4549) — SUPPORTED
- [x] `ContractLevelChecker` duplicate fn/event, external clash, hash collision (1686/5883/9914/1860) — SUPPORTED
- [x] `ContractLevelChecker` base-ctor arity (3415) + given-twice (3364) — SUPPORTED; bare-modifier 1563 → **CL1 over-accept**
- [x] `ContractLevelChecker` library (9469/9957) + interface + abstract (3656/9348/9571) requirements — SUPPORTED
- [x] `DeclarationTypeChecker` recursive struct (2046), array length (1406/3208/3658; 1847 minor), mapping key (7804), enum size (1611), UDVT (8657/8129) — SUPPORTED
- [x] `abi.encodePacked` validation predicate — AE1 **resolved** (non-divergence); nested-array → **PK1 over-reject**
- [x] `new`-contract creation type rules (interface/library/abstract) — SUPPORTED
- [x] `TypeChecker` overload-resolution ambiguity over literals — CONFIRMED non-divergent
- [x] `PostTypeChecker` constant cyclic dependency (6161) — **PT1 fixed** (`constantsHaveCycle`)

**Still NOT reached (worklist for a future pass):**

- `abiDecodingFunctionStruct` nested-struct decode into memory + free-memory-
  pointer discipline at the **emitted-Yul (codegen) level** — rounds 1-2 confirmed
  the observable; the allocation sequence itself was not re-derived and is not
  independently reachable from Solidus's value-level interpreter.
- `using`-for directive legality (global `using`, operator `using`, `using` on
  the wrong type) — `UsingDecl.checkContractLevel` (`TypeCheck.lean:11929`) exists
  but was not exhaustively cross-checked against solc's `using` rules this round.
- `ControlFlowRevertPruner` full algorithm vs Solidus terminal-pruning — remains
  **CF2 IN-FLIGHT** (sibling arc); adjacent unreachable-code-after-return is a solc
  **warning** only (both accept), not an acceptance divergence.
- Storage-layout specifier rules (`checkStorageLayoutSpecifier` 7587/8894) and
  `checkStorageSize` (7676/5026 too-much-storage) — headline-only; a
  256-slot-overflow probe would confirm parity.
- String / hex / unicode literal checksum and escape validation edge cases —
  performed by solc before AST export (importer-masked); not independently
  modeled.

---

## 8. Bottom line

Reading the previously-unreached declaration- and contract-level acceptance
surfaces — `ContractLevelChecker` (receive/fallback, duplicates, external
clashes, hash collisions, base-constructor arguments, library/interface/abstract
requirements), `ImmutableValidator`, `DeclarationTypeChecker` (recursive struct,
array length, mapping keys, enum, UDVT), the `abi.encodePacked` validation
predicate, `new`-contract type rules, and `TypeChecker` overload resolution —
surfaced **no new wrong-value or wrong-order soundness divergence**, matching
rounds 1-2.

Two round-2 INFERRED items are closed (AE1 is a non-divergence; PT1 is fixed) and
the immutable exactly-once worry is fully cleared. The two NEW divergences are
acceptance-boundary: **PK1**, a live over-reject where Solidus refuses
`abi.encodePacked` of a nested value-array (`uint[2][3]`) that solc encodes; and
**CL1**, a niche, importer-masked over-accept where Solidus accepts a bare
modifier-style base-constructor call on a zero-parameter base that solc rejects
(1563). Neither changes a computed value.
