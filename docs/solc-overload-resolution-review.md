# solc vs solidity-lean: function overload resolution & related name resolution

Adversarial review of function **overload resolution**, argument
convertibility, ambiguity detection, function-value selection, and
selector/signature-clash detection. Method: read solc 0.8.35 source
(`libsolidity/analysis/TypeChecker.cpp`, `libsolidity/ast/Types.cpp`,
`libsolidity/analysis/ContractLevelChecker.cpp`), probe the pinned binary
`solc-0.8.35` (LEGACY codegen), then trace solidity-lean
(`SolidCore/Solidity/TypeCheck.lean`, `Interface.lean`) by file:line.

Scope reminder (already-mined, not re-reviewed): user-defined operators &
using-for binding, C3/override order, modifier/super dispatch, abi.encodeCall
selector (EC1), external-function-values.

---

## Finding 1 (CONFIRMED) — free functions shadowed by a contract member are NOT removed from the overload candidate set

**Classification:** over-accept **and** over-reject (same root cause).
**Severity:** medium. **Confidence:** high (solc probes + exact Lean file:line;
the same shadowing IS implemented for errors/events, so this is a plain
omission for functions).

### Root cause

solc removes a file-level (free) function from a contract's name scope when the
contract (or a base) declares any function with the same **name** — a bare
`f(...)` inside the contract resolves only among the contract's own `f`
overloads; the free `f` is not a candidate at all (name-based shadowing, emits
warning 2519 "This declaration shadows an existing declaration").

solidity-lean builds the call-site resolution environment as
`env.functions := visibleFunctionSigs ++ sourceFunctions`
(`TypeCheck.lean:12786`), where `sourceFunctions` is the **full** list of free
function sigs (`freeFunctionSigs`, `TypeCheck.lean:13467`, passed unfiltered to
every `ContractDecl.check`, `TypeCheck.lean:13555` / param at `12620`). No
name-based removal of shadowed frees is performed. Call resolution
(`FunctionSigs.resolveChecked env.types env.functions name ...`,
`TypeCheck.lean:5828`) then iterates this flat list, matching purely by name +
argument convertibility (`resolveCheckedLoop`, `TypeCheck.lean:3485`), with no
member-over-free precedence.

Note the asymmetry that pins this as an omission: Lean **does** implement exactly
this shadowing for **errors** and **events** —
`ErrorSigs.withoutNamesOf errorSigs sourceErrors` and
`EventSigs.withoutNamesOf eventSigs sourceEvents` (`TypeCheck.lean:12676-12677`,
`12758-12763`) drop source-level errors/events whose names collide with contract
members. There is no analogous `FunctionSigs.withoutNamesOf` for functions.

### Repro A — over-accept (solc rejects, Lean accepts)

```solidity
pragma solidity 0.8.35;
function f(uint256 a) pure returns (uint) { return a + 1; }   // free
contract C {
    function f(string memory s) internal pure returns (uint) { return bytes(s).length; }
    function g() internal pure returns (uint) { return f(5); } // 5 matches only the free f
}
```

- **solc** (`solc-0.8.35`): rejected. The member `f(string)` shadows the free
  `f(uint256)`, so the only candidate is `f(string)`:
  `Error: Invalid type for argument in function call. Invalid implicit
  conversion from int_const 5 to string memory requested.`
  (plus warning 2519 for the shadow).
- **solidity-lean**: the free `f(uint256)` remains in `env.functions`;
  `resolveCheckedLoop` finds it (member `f(string)` fails `matchesCheckedArgs`
  for `5`, free `f(uint256)` succeeds via `implicitLiteralFits`), returns it,
  and the call is accepted — resolving to a function solc says is out of scope.

### Repro B — over-reject (solc accepts, Lean rejects)

```solidity
pragma solidity 0.8.35;
function f(uint256 a) pure returns (uint) { return a + 1; }   // free
contract C {
    function f(uint256 s) internal pure returns (uint) { return s + 9; }
    function g() internal pure returns (uint) { return f(5); }
}
```

- **solc**: accepted (warning 2519 only). The member shadows the free `f`; the
  call runs the member (`s + 9`).
- **solidity-lean**: both `f(uint256)` sigs sit in `env.functions`; both match
  `f(5)`. They are not `FunctionSig.sameResolutionTarget` (the member sig has
  `visibility = some internal_`, the free sig has `visibility = none` —
  `FunctionDecl.signature?`, `TypeCheck.lean:1975`; the check compares
  visibility at `TypeCheck.lean:2166`), so `resolveCheckedLoop` reports
  `TypeError.ambiguousFunction` (`TypeCheck.lean:3499`). This is the more
  dangerous direction: because solc accepts Repro B, a solc-AST-derived fixture
  containing a member/free name collision would be **rejected** by the Lean
  frontend.

### Suggested fix (not applied — review only)

Mirror the errors/events treatment: before forming `env.functions`, drop free
function sigs whose name appears among the contract's visible member function
names, e.g. a `FunctionSigs.withoutNamesOf` filtering `sourceFunctions` by
`visibleFunctionSigs.map (·.name)` (and, to match solc, inherited member names).

---

## Verified faithful (clean negatives)

Each probed on `solc-0.8.35` and traced in Lean; no divergence found.

1. **Unique-match / ambiguity rule.** solc collects candidates that accept the
   args by implicit conversion and requires exactly one, with **no**
   most-specific tiebreak (`TypeChecker::visit(Identifier)`,
   `TypeChecker.cpp:3805-3839`; `resolveOverloads`, `3091-3133`). Lean mirrors
   this: candidate filter by `matchesCheckedArgs` then uniqueness with a
   `sameResolutionTarget` de-dup for genuine duplicates
   (`resolveCheckedLoop`, `TypeCheck.lean:3485-3506`). Confirmed both **ambiguous**
   (not most-specific) for: `f(uint8)/f(uint256)` called with a `uint8` var;
   `f(bytes2)/f(bytes4)` with a `bytes2` var; `f(address)/f(address payable)`
   with an `address payable` var; `f(uint256)/f(int256)` with literal `5`;
   `f(bytes memory)/f(string memory)` with a string literal. All error
   "No unique declaration found after argument-dependent lookup" in both.

2. **Convertibility that narrows the candidate set.** `Derived` arg to
   `f(Base)/f(address)` resolves uniquely to `f(Base)` (contract→base yes,
   contract→address no) — solc accepts, Lean accepts via
   `TypeContext.canImplicitlyConvert` contract-ancestor arm
   (`TypeCheck.lean:1262-1265`). `uint[2] memory` to `f(uint[2])/f(uint[])`
   resolves uniquely (no memory fixed→dynamic implicit conversion). `uint256`
   to `f(MyIntUVT)/f(uint256)` resolves uniquely to `f(uint256)` (no implicit
   wrap). All match. `Ty.canImplicitlyConvert` (`TypeCheck.lean:1049`) also
   correctly forbids all implicit signed↔unsigned integer conversions.

3. **Overloading across inheritance.** Base `f(uint256)` + derived `f(string)`:
   both participate, each call resolves — Lean merges via
   `addNonPrivateAllIfNewSignature` (`TypeCheck.lean:12764-12768`,
   `env.functions` at `12786`). Base `f(uint256)` + derived `f(int256)` called
   with `5`: ambiguous in both. Derived redeclaring an inherited signature
   without `override`: rejected by both (override checker).

4. **Function selected as a VALUE (function pointer).** solc does **not**
   type-direct overload selection for a bare function used as a value; two
   in-scope overloads → error even when an expected function type would
   disambiguate (`!annotation.arguments` branch, `TypeChecker.cpp:3788-3804`;
   probed: two internal `f` to a `function(uint256) internal` slot →
   "No matching declaration found after variable lookup"; two external via
   `this.f` → "Member not unique"). One internal + one external overload
   resolves (external not a bare-`f` candidate). Lean mirrors exactly:
   `resolveInternalFunctionValueByName` / `resolveExternalFunctionValueByName`
   filter by callability then require uniqueness with no type direction
   (`TypeCheck.lean:2366-2416`), and `resolveInternalFunctionValueAssignableTo`
   only type-checks *after* a unique name resolution (`2418-2427`).

5. **Named arguments.** `f({a: 1, ...})` matching requires the param-name set to
   equal the arg-name set (`ArgInfos.orderedTys?` / `collectNamed?`,
   `TypeCheck.lean:2086-2106`), matching solc `canTakeArguments`
   (`Types.cpp:3564-3585`). Overloads with a shared param name both survive →
   ambiguous, as in solc.

6. **Selector / external-signature clash detection.** solc's two checks —
   `checkExternalTypeClashes` (9914: same external signature, differing param
   types, across the full linearization) and `checkHashCollisions` (1860:
   4-byte keccak collision over `interfaceFunctionList`) —
   `ContractLevelChecker.cpp:466-517`. Lean canonicalizes ABI types correctly
   through the type context — contract→`address`, enum→`uint8`,
   user-value-type→underlying, library param→none, struct→tuple
   (`TypeContext.abiCanonicalFuel?`, `TypeCheck.lean:910-985`, resolving
   `Ty.user` by context, unlike the location-free `Ty.abiCanonical?` in
   `Interface.lean:2426`) — and runs
   `ensureNoDuplicateExternalAbiSelectors` over the **full dispatch order**
   (`TypeCheck.lean:12769-12770`), so an external-signature clash across
   inheritance is caught by selector equality even though
   `ensureNoDuplicateExternalAbiSignatures` (`12659`, `12742`) only scans direct
   functions. Same-signature duplicates and real keccak collisions are both
   rejected.

---

## Summary

One confirmed divergence: **free functions shadowed by a same-named contract
member are not removed from solidity-lean's overload candidate set**
(`env.functions` at `TypeCheck.lean:12786`), producing an over-accept when a
call matches only the shadowed free function and an over-reject
(`ambiguousFunction`) when a call matches both — while the identical shadowing
IS implemented for errors and events (`withoutNamesOf`, `TypeCheck.lean:12676`).
The rest of the overload surface — unique-match/ambiguity semantics (no
most-specific tiebreak), argument convertibility, cross-inheritance overloads,
function-value selection, named arguments, and selector/signature-clash
detection — was probed against the pinned solc and found faithful.
