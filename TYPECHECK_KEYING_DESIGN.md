# R4: source-keyed conversion predicates + per-receiver-type member table

Rearchitecture phase 4 (final). Target file: `SolidCore/Solidity/TypeCheck.lean`.

## Problem

The acceptance layer's conversion predicates were flattened `(shape × shape)`
match tables ending in `| _, _ => false` sinks. solc structures the same logic
as *per-source-type virtual dispatch* (`Types.h:224-227`): every `Type`
subclass overrides `isImplicitlyConvertibleTo` / `isExplicitlyConvertibleTo`,
so the C++ vtable makes it impossible to "forget" a source type — each source
type's conversion story is one closed method. Our flattened tables had the
dual failure mode: a forgotten cell silently became `false` (over-reject,
replay-reachable). Bug-fixes #121/#170/#181 each landed as individual cells.

## Shape after R4

### 1. `Ty.canExplicitlyConvert` (source-keyed)

Layer order preserved exactly:

1. **Untyped-literal layer** (`exprIsUntypedNumberLiteralExpression`): kept as
   the leading concern — it genuinely is one in solc
   (`RationalNumberType::isExplicitlyConvertibleTo`, Types.cpp:1042-1064).
   Factored into `canExplicitlyConvertUntypedLiteral` keyed on the TARGET
   (that is solc's own shape for the rational layer).
2. **Identity** (`actual == target`), as solc's per-type methods all accept
   identity (and `actual == target` short-circuit predates R4).
3. **Source-keyed dispatch**: `match actual with` — one arm per `Ty`
   constructor, EXHAUSTIVE (no `| _ =>` sink over the source), each arm a
   small target predicate named `explicitFrom<Source>` mirroring the
   corresponding solc method:
   - `address p` → `explicitFromAddress` (AddressType::isExplicitlyConvertibleTo, Types.cpp:495-510)
   - `uint`/`int` → `explicitFromInteger` (IntegerType::…, Types.cpp:627-646)
   - `fixed`/`ufixed` → `explicitFromFixedPoint` (FixedPointType::…, Types.cpp:791-794)
   - `bytesN`/`fixedBytes` → `explicitFromFixedBytes` (FixedBytesType::…, Types.cpp:1360-1377)
   - `bool` → identity only (Type base default, Types.h:224-227)
   - `bytes`/`string` → `explicitFromByteArray` (ArrayType::…, Types.cpp:1668-1680: bytes↔string, bytes→bytesNN)
   - `array` → identity only in this model (general ArrayType explicit conv beyond
     byte-arrays is location-dependent and handled elsewhere/not accepted here)
   - `user path` → `explicitFromUser` — sub-keyed by what the path IS
     (contract / enum / UDVT / struct), mirroring ContractType (Types.cpp:1491-1499),
     EnumType (Types.cpp:2674-2681), UserDefinedValueType (base default; wrap/unwrap
     are calls, not conversions).
   - `mapping`/`tuple`/`struct`/`enum`(core)/`functionWithLocations` → identity
     only (base default / FunctionType kind rules not reachable in this AST layer).

   The *string-typed-source* literal-fit escape hatches the old table carried
   (`typeConversionLiteralFits target sourceExpr` disjuncts in non-literal
   rows) are preserved verbatim inside the relevant arms — they cover
   negated/complex literal expressions the leading layer's
   `exprIsUntypedNumberLiteralExpression` recognizes but whose `actual` was
   inferred; behavior-preservation demands they stay.

### 2. `Ty.canImplicitlyConvert` + `TypeContext.canImplicitlyConvert`

Same source-keying for the context-free core (`implicitFrom<Source>` arms,
exhaustive over the source constructor). The context-aware
`TypeContext.canImplicitlyConvert` gains a `storageCopy : Bool := false`
flag and becomes THE one recursion for arrays, mirroring
`ArrayType::isImplicitlyConvertibleTo` (Types.cpp:1628-1666):

- `storageCopy := false` (every existing call site): arrays require identical
  element type + same sizedness/length — exactly the old `==`-only behavior
  (solc's "conversion to storage pointer or to memory" branch: same base
  type, same dynamic-sizedness, same length ⇒ only identity is accepted in
  our location-free `Ty`).
- `storageCopy := true` (the storage-copy assignment site, old
  `Ty.storageArrayCopyAssignable?`): solc's "less restrictive since we copy
  anyway" branch — dynamic dest accepts any source length; fixed dest `T[N]`
  needs fixed source `S[M]`, `M ≤ N`; element recursion via the same
  function with the flag kept ON (nesting under a storage array stays a
  storage copy); leaf = context-aware implicit convertibility. The
  legacy-codegen struct-direct-element carve-out stays at the OUTER wrapper
  (`Ty.storageArrayCopyAssignable?`, now a thin wrapper over the unified
  recursion), because it is a codegen limit, not a conversion rule.

Callers of context-FREE `Ty.canImplicitlyConvert` audited (see section
"Context-free callers" below).

### 3. Per-receiver-type builtin member table

New `TypeContext.builtinValueMemberInfo?` = one lookup consulted by
`checkNonStructMember`, built from a per-receiver-type table
`builtinValueMembers : TypeContext → Ty → List (Name × BuiltinMemberInfo)`
mirroring `Type::members()`:

```
structure BuiltinMemberInfo where
  ty : Ty                     -- member's value type
  needsStateRead : Bool       -- balance/code/codehash read chain state
  minEvm : Option EvmVersion  -- codehash ⇒ constantinople
```

- `address(±payable)` → balance/code/codehash (+ transfer/send/call/
  delegatecall/staticcall exist ONLY in call position in this model — the
  table records the value-position members; the call-position name sets
  `Ty.isAddressCallMemberName` remain and are cross-referenced).
- `bytes`/`string`/`array _ _`/`bytesN`/`fixedBytes` → `length` per
  `hasLengthMember` (push/pop are call-position, handled at the call check).
- external `functionWithLocations` → selector/address (value position covered
  by the earlier dedicated `.selector`/`.address` match arms and the
  `abiTyWithEnv?` fallback; the table is consulted first for the reserved
  names).

The uniform rule in `checkNonStructMember`: if `member` is a RESERVED builtin
name (`builtinReservedMemberNames`), it must appear in the receiver's table
(else the same per-name error as before: `expectedType address` for
balance/code/codehash, `unsupported "length member…"` for length); otherwise
the existing `abiTyWithEnv?` fallback runs unchanged. This preserves every
current accept/reject: a reserved name on a wrong receiver cannot leak into
the fallback (which would have over-accepted `x.balance` on non-address).

Meta-type members (`type name` receiver: min/max on int/uint and enums,
enum cases, contract name/creationCode/runtimeCode/interfaceId) stay in the
`Expr.typeName` arm but are routed through a companion table
`builtinMetaMemberInfo?` where the result type is context-free; the
contextual GATES (abstract/interface, self-reference cycle, immutable-set)
remain explicit requires — they are acceptance conditions of the OCCURRENCE,
not of the member's existence, matching solc (members exist; TypeChecker
gates usage).

### 4. `Ty.commonImplicit?` fallback — DONE (with a solc-verified fix)

`TypeContext.commonImplicit?` (new) shares the numeric/address/fixed-bytes
common-type table with `Ty.commonImplicit?` and routes only the DIRECTIONAL
FALLBACK through the context-aware convertibility — exactly solc
`Type::commonType` (Types.cpp:279-295), whose fallback calls the full
virtual `isImplicitlyConvertibleTo`. The `TypeContext` is threaded through
the operand-commoning family (`commonArrayElementTy?` → `commonOperandTy?`
→ `commonCheckedTyFor` → `arithmeticTy`/`bitwiseTy`/`relationalTy` and the
inline-array element commoning). The context-free `Ty.commonImplicit?`
remains ONLY for the bare-literal inline-array bottom-up typing
(`inlineArrayBottomUpTyFuel?`), where every operand is an integer mobile
type and user-type rules cannot fire.

GENUINE FIX (pinned-solc probes, 2026-07-12):
`Base[2] memory arr = [derived, base];` — solc 0.8.35 ACCEPTS (probe2.sol,
importer-verified), the pre-R4 model rejected ("array literal common
type"): fixed. `[base, unrelatedOther]` — solc REJECTS ("Unable to deduce
common type for array elements", probe3.sol): still rejected. Both pinned
in `SolidCore/Witness/TypeCheckKeying.lean`. `d == b` (Derived vs Base)
was ALREADY accepted pre-R4 via the dedicated contract-comparison
dispatch (probe1.sol, verified unchanged).

## Differential-matrix method

`scratchpad/audit-r4/Matrix.lean` (not part of the repo build):

- a fixed `TypeContext` with contracts `C` (payable receive), `N`
  (non-payable), `D` (derived from `C`), library `L`, interface `I`, enums
  `E`/`E2`, UDVTs `U`(uint256)/`U8`(uint8), struct `S`;
- a ~45-type grid covering every constructor incl. widths/signs/bytesN sizes/
  address±payable/user variants/function mutabilities/nested arrays;
- BEFORE snapshot at the pre-rewrite commit, AFTER snapshot re-run per
  target commit; any line diff must be reverted or pinned-solc-justified.

Predicates snapshotted per pair: `Ty.canImplicitlyConvert`,
`TypeContext.canImplicitlyConvert`, `Ty.storageArrayCopyAssignable?`,
`Ty.commonImplicit?`, `Ty.canExplicitlyConvert` with a non-literal source
expr, plus literal-source rows (0, 1, 300, -1, 2^170, "abc", 0x…20-byte hex)
× all targets. Member grid: `checkExpr` verdict for every (receiver-type ×
member-name) pair in value position AND `type(T).member` position.

Snapshot summary and change list: see `audit-r4/` artifacts + final report.

## Context-free callers of `Ty.canImplicitlyConvert` (audit — RESULT)

1. **DELETED (dead code)**: the whole context-free resolver family —
   `FunctionSig.paramsAccept`/`matchesArgs`, `ModifierSig.paramsAccept`/
   `matchesArgs`, `EventSig.matchesArgs`, `ErrorSig.matchesArgs`,
   `FunctionSigs/ModifierSigs/EventSigs/ErrorSigs.resolve(+Loop)`,
   `TypeContext.resolveContractMemberFunction`,
   `requireFunctionArgsAccept`. Every LIVE resolution path goes through the
   context-aware `matchesCheckedArgs` → `canAssignToWidenIn` machinery
   (verified by repo-wide grep + full build). This closes the split-brain
   rather than patching dead code.
2. **JUSTIFIED**: `CheckedExpr.canImplicitlyAssignTo`/`canAssignTo`/
   `expectAssignableTo`/`expectImplicitlyAssignableTo` — every live call
   site passes a BUILTIN expected type (uint256/bytes32/bytes/string/
   bytesN4/uint8: mulmod/ecrecover args, index/slice bounds, low-level call
   value/gas, blockhash, etc.), where the context rules (user aliases,
   contract covariance) cannot fire.
3. **FIXED (target 4)**: `Ty.commonImplicit?`'s directional fallback — see
   §4.
4. **JUSTIFIED**: `inlineArrayBottomUpTyFuel?` — bare-number-literal
   mobile types only; `FunctionSig.internalFunctionValueAssignableTo` and
   the using-for receiver bind already use the context-aware predicate.
