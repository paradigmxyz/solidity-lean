# solc 0.8.35 public state-variable getter review (solidity-lean)

Search-only differential review of auto-generated `public` state-variable getters
(signature synthesis, argument flattening for mappings/arrays, struct-member
omission, scalar/string/bytes/constant/immutable getters) against pinned
solc 0.8.35.

## Summary

- **3 real divergences found**, all sharing one root cause: solidity-lean's
  struct-getter member-omission rule **recurses into nested struct members**,
  whereas solc's rule is **shallow** (only the *direct* members of the returned
  struct are examined; a nested struct member is always kept whole, and if that
  nested struct is not externally returnable solc **errors** rather than dropping
  it). solidity-lean also lacks solc's two getter-level rejection checks
  (error 6744 "Internal or recursive type", error 5359 "all members omitted").
- Everything else checked is a **clean negative**: scalar getters, string/bytes
  scalar getters, mapping/nested-mapping arg order, array-index args, 2D arrays,
  mapping→array combos, and the *top-level* struct member-omission rule all match
  solc.

Root cause (two mirror copies of the same rule):
- `SolidCore/Solidity/Interface.lean:2385` `Ty.omittedFromStructPublicGetter?`
  — cases `Ty.tuple`/`Ty.struct` recurse (lines 2389-2392) and report a member
  as omitted if it *transitively* contains a mapping or array.
- `SolidCore/Solidity/TypeCheck.lean:850` `Ty.omittedFromStructPublicGetter?`
  — same recursion (lines 855-862), consumed by `structGetterReturnTys`
  (line 882) and the getter validation in `StateVarDecl.check`
  (`TypeCheck.lean:9659-9677`), which never enforces solc's 6744/5359 errors.

solc ground truth: `libsolidity/ast/Types.cpp:2868`
`FunctionType::FunctionType(VariableDeclaration const&)` — struct branch
(lines 2898-2915) only skips a member when it is *directly* a `Mapping` or a
*direct* array that is not byte-array/string; nested structs are pushed whole.
Rejections at `libsolidity/analysis/TypeChecker.cpp:548-556`.

---

## Divergence 1 — nested struct member containing an array is dropped instead of returned

**Confidence: 90%. Severity: wrong-signature / wrong-return.**

Program:
```solidity
pragma solidity 0.8.35;
contract C {
    struct Inner { uint a; uint[] arr; }
    struct Outer { uint x; Inner inner; }
    Outer public o;
}
```

solc getter (`--abi`, selector `o()`):
```
o() view returns (uint256 x, (uint256 a, uint256[] arr) inner)
```
solc keeps `inner` whole (it is a struct, not a direct mapping/array), so the
`uint[] arr` *inside* the nested struct is returned.

solidity-lean: `Ty.omittedFromStructPublicGetter?` recurses into `Inner`, finds
`Ty.array`, and reports `inner` as omitted. The generated getter is
`o() returns (uint256)` — a single field, `inner` dropped entirely. A caller ABI-
decoding the return gets a different tuple. Accepted (not rejected), so this is a
silently wrong getter shape.

---

## Divergence 2 — nested struct member containing a mapping is accepted (solc rejects)

**Confidence: 90%. Severity: over-accept (+ wrong-return).**

Program:
```solidity
pragma solidity 0.8.35;
contract C {
    struct Inner { uint a; mapping(uint=>uint) m; }
    struct Outer { uint x; Inner inner; }
    Outer public o;
}
```

solc: **compile error 6744** —
`Internal or recursive type is not allowed for public state variables.`
(a nested struct with a mapping cannot be externalized, so the getter has no
valid interface type).

solidity-lean: recurses into `Inner`, finds the mapping, drops `inner`, and
produces getter `o() returns (uint256)`. The `StateVarDecl.check` validation
(`TypeCheck.lean:9666-9677`) only inspects the *already-omitted* return list, so
the non-returnable member is never flagged. Over-accepts a program solc rejects.

---

## Divergence 3 — struct getter with all members omitted is accepted (solc rejects)

**Confidence: 88%. Severity: over-accept.**

Program:
```solidity
pragma solidity 0.8.35;
contract C {
    struct S { mapping(uint=>uint) m; uint[] arr; }
    S public s;
}
```

solc: **compile error 5359** —
`The struct has all its members omitted, therefore the getter cannot return any values.`

solidity-lean: `structGetterReturnTys` yields `[]`; `StateVarDecl.check`'s
`firstNonAbiEncodable?`/`firstAbiCoderV2Only?` on the empty list both return
`none`, so the contract is accepted and a getter with **zero** return values is
generated. solc has an explicit guard (`TypeChecker.cpp:552-553`); solidity-lean
has none. Over-accepts.

---

## Clean negatives (verified, matches solc)

- **Top-level struct omission (mission #5).** `struct S { uint a; string b;
  mapping(uint=>uint) c; uint[] d; bytes e; } S public s;` — solc returns
  `(uint256 a, string b, bytes e)`, dropping the mapping `c` and the array `d`
  while **keeping** `string` and `bytes`. solidity-lean's rule (bytes/string are
  distinct `Ty.bytes`/`Ty.string`, not `Ty.array`) produces exactly the same
  return. Verified against solc `--abi`.
- **Nested struct with only value members.** `struct Inner { uint a; bool b; }
  struct Outer { uint x; Inner inner; } Outer public o;` — both solc and
  solidity-lean keep `inner` and return `(uint256 x, (uint256 a, bool b) inner)`.
- **Mapping / nested-mapping arg order (mission #2).** `Ty.publicGetterShape?`
  (`Interface.lean:2423`, `TypeCheck.lean:899`) accumulates keys outer→inner
  (`key :: tail.fst`), matching solc's while-loop
  (`Types.cpp:2876-2896`): `mapping(address=>mapping(uint=>bool))` →
  `mm(address,uint256) returns (bool)`.
- **Array-index args (mission #3).** Each array dimension contributes one
  `uint256` index parameter and the return is the *element*, not the whole array:
  `uint[] public arr` → `arr(uint256) returns (uint256)`;
  `uint[][] public a` → `a(uint256,uint256) returns (uint256)`. Matches solc.
- **Mapping→array / combos (mission #4).** `mapping(uint=>uint[]) public ma` →
  `ma(uint256,uint256) returns (uint256)` (key then index, outer→inner). Matches.
- **String/bytes scalar getter (mission #9).** `string public name` /
  `bytes public b` → `name()`/`b()` returning the whole value
  (`toCoreByteStringGetterIfPublic?`, `Interface.lean:19659`); byte arrays break
  out of solc's while-loop (`Types.cpp:2887`) and are returned whole. Matches.
- **constant / immutable getters (mission #7).** Distinct code paths
  (`toCoreConstantGetterIfPublic?` `Interface.lean:19720`,
  `toCoreImmutableGetterIfPublic?` `19743`) emit `C()`/`I()` with the value.
  Consistent with solc.

## Notes / scope

Findings 1-3 are established by (a) reading the exact Lean functions and the
solc `FunctionType(VariableDeclaration)` constructor + TypeChecker guards, and
(b) confirming solc 0.8.35's output/errors on the minimal programs above
(`--abi` for D1 shape, compile errors 6744/5359 for D2/D3). I did not execute the
solidity-lean interpreter end-to-end on these programs; the Lean-side conclusions
are a static trace of `omittedFromStructPublicGetter?` →
`structGetterReturnTys`/`publicGetterShape?` → `StateVarDecl.check`, hence the
~90% (not 100%) confidence. A single fix — making the omission rule shallow and
adding the 6744/5359 rejections — resolves all three.
