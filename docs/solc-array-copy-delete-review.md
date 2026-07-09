# solc vs solidity-lean — array/aggregate COPY / RESIZE / DELETE review

Ground truth: pinned solc 0.8.35 (`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`),
**LEGACY codegen** (optimizer=false, no via-ir) — the harness's compilation mode.
Interpreter under test: `SolidCore/Solidity/Interpreter.lean` + `TypeCheck.lean`.
Method: for each candidate, a minimal Solidity program was compiled by pinned solc
(legacy) and run under Forge for the value/slot ground truth, then imported through
`scripts/solc_ast_to_lean_source.py` and executed under the Lean interpreter via
`checkedCallWord*Matches`, comparing element read-backs (which observe exact packed
slot state, since `push()`/regrow relies on vacated slots being physically zero).

---

## DIVERGENCE 1 — over-accept: memory/calldata copy of a **struct-element array** into storage
**Confidence: 98%. Severity: over-accept (accepts a program pinned legacy solc refuses to compile).**

solc 0.8.35 **legacy** rejects, at compile time, copying an array whose *element base
type is a struct* (a non-value, non-array type) from **memory or calldata** into storage.
This is the `solUnimplementedAssert` in `ArrayUtils::copyArrayToStorage`
(`libsolidity/codegen/ArrayUtils.cpp:76-85`):

> Error: Copying of type `struct S memory[] memory` to storage is not supported in
> legacy (only supported by the IR pipeline). Hint: try `--via-ir`.

It fires only for the "base type is not an Array and not a value type" case, i.e. the
element is a **struct**. It applies to both dynamic `S[]` and fixed `S[N]` sources, from
memory and from calldata.

solidity-lean **accepts and executes** all three, producing the via-ir result:

| program (element = struct S)                         | pinned solc legacy | solidity-lean |
|------------------------------------------------------|--------------------|---------------|
| `S[] memory m; arr = m;`   (dynamic, memory)         | COMPILE ERROR      | accepts, `f()`→4 |
| `S[2] memory m; arr = m;`  (fixed, memory)           | COMPILE ERROR      | accepts, `f()`→9 |
| `function f(S[] calldata m){ arr = m; }` (calldata)  | COMPILE ERROR      | accepts (typechecks) |

Minimal reproducer (dynamic/memory):
```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
struct S { uint256 a; uint256 b; }
contract C {
    S[] arr;
    function f() external returns (uint256) {
        S[] memory m = new S[](2);
        m[0] = S(1,2); m[1] = S(3,4);
        arr = m;            // legacy solc: "not supported in legacy"
        return arr[1].b;    // solidity-lean returns 4
    }
}
```
- `solc --bin` (legacy) → `Error: Copying of type struct S memory[] memory to storage is not supported in legacy (only supported by the IR pipeline).`
- Lean: `importedContractAccepted = true`; `checkedCallWordMatches … "f" … 4 = Except.ok true`.

**Boundary (verified):** what solc legacy *accepts* and solidity-lean also accepts (no
divergence): `string[] memory→storage`, `bytes[] memory→storage`, `uint256[][] memory→storage`
(nested value arrays — base is an Array category), and top-level `S memory→storage` struct
assignment whose members include a `uint256[]`. The over-accept is specific to an **array
whose immediate element is a struct**, copied from memory/calldata.

**Root cause.** The assignment typechecker accepts `storageArray = <rhs>` via
`Ty.storageArrayCopyAssignable?` (`TypeCheck.lean:1126-1136`) or the general
`expectAssignableToIn` fallback (`TypeCheck.lean:7317-7322`). Neither path consults the
**source data location** together with the **element being a non-value type**; there is no
"legacy cannot copy struct-array from memory/calldata to storage" rule. The interpreter
then executes the copy through `storeStorageLayoutAtWithDeepClear`
(`Interpreter.lean:3784-3861`), which handles struct elements fine — matching via-ir, not
legacy. Because the fixture ground truth is legacy, any such program has no compilable
solc counterpart, so this is a latent over-accept rather than a wrong-value bug.

Note: through the *importer* specifically, the `struct-defined-inside-contract` form is
incidentally rejected by a nominal name mismatch (state var element `C.S` vs local element
`S`), which masks the over-accept. Defining the struct at file scope (so both sides resolve
to `S`) removes the mask and exposes the acceptance. The underlying typechecker rule is the
same either way.

---

## Clean negatives (verified matching; no divergence)

All of the following were run both under pinned solc legacy (Forge) and the Lean
interpreter and **agreed**. These are the operations solc lowers specially; the interpreter's
slot-level model (`StorageLayout` + `wordBitRange`/`wordReplaceBitRange` sub-word masking)
reproduces them.

1. **Packed `.pop()` sub-word clearing.** `uint128[]` (2/slot): `push(A); push(B); pop(); push();`
   → `(A, 0)`. solc clears only B's sub-word so the later no-arg `push()` zero-inits; Lean
   matches. (`Interpreter.lean:4406-4453`, `clearStorageLayoutAtDeep` packed arm 3707-3712.)
2. **Packed `delete arr[i]` sub-word clearing.** `uint128[]`: `push(0x1111); push(0x2222);
   delete a[1];` → `(0x1111, 0)`. Sibling preserved, deleted sub-word cleared. Matches.
3. **memory→storage shrink, packed tail cleared.** `uint128[]` len3 `= uint128[] memory` len1,
   then `push()` → `(D1, 0)`. Vacated packed sibling cleared. Matches.
   (`storeStorageLayoutAtWithDeepClearFuel` + `clearDynamicArrayLayoutTail`, 3770-3859.)
4. **storage→storage shrink, packed tail cleared.** `a(len3) = b(len1)` then `push()` → `(F1, 0)`. Matches.
5. **Odd-width `bytesN[]` packing** (`bytes3[]`, 10/slot): `push; push; pop; push();` →
   `(0x111111, 0)`. Per-slot count `32/3` and sub-word offsets correct. Matches.
6. **`delete` of a whole packed dynamic array zeroes data slots.** `uint128[]` len3, `delete d;`
   then 4×`push()` → `(0,0,0,0)` (regrow sees physically-zero slots). Matches.
   (`deleteStorageField`→`clearStorageLayoutAtDeep`, `Interpreter.lean:3964-4009`.)
7. **`bytes` short→long transition on push.** memory `bytes(31)` → storage (short in-slot),
   `s.push(0xCD)` → length 32 (long, separate `keccak(slot)` data). `(length, s[0], s[31]) =
   (32, 0xAB, 0xCD)`. Matches solc's in-place transition. (`storeStorageBytesAt` 3096-3115.)
8. **int8[] storage→memory deep copy sign-extends.** `e.push(-1); e.push(5); int8[] memory m = e;`
   → `(uint256(int256(m[0])), …) = (2^256-1, 5)`. Packed signed unpack via `packedStorageValueFromWord?`
   (`Interpreter.lean:3196-3201`, 3175). Matches.
9. **Nested value arrays memory→storage.** `uint256[][] memory → storage`; `(f.length, f[0][1],
   f[1][0]) = (2, 8, 9)`. Matches (legacy supports value-base / array-base elements).
10. **`arr.length = n` rejected** (removed in 0.6.0). `.length` member is `lvalue=false`
    (`TypeCheck.lean:5627-5634`); assignment requires an lvalue (`TypeCheck.lean:3073`), so
    solidity-lean rejects it — matching solc.
11. **`struct S[] storage → storage` copy accepted** (solc legacy supports it; source is not
    memory/calldata) — solidity-lean accepts and executes. No over-reject.

---

## Summary

- **1 confirmed divergence (over-accept, 98%):** memory/calldata copy of a *struct-element*
  array (`S[]` / `S[N]`) into storage — hard legacy compile error in solc 0.8.35, accepted
  and executed by solidity-lean. Root cause: `TypeCheck.lean:7317-7322` /
  `Ty.storageArrayCopyAssignable?` (1126) never encode the legacy source-location + non-value
  element restriction; interpreter executes it via `Interpreter.lean:3784-3861`.
- **11 clean negatives** across packed pop/delete/shrink, odd-width `bytesN` packing,
  whole-array delete data-slot zeroing, `bytes` short↔long transition, signed packed
  storage→memory unpack, nested value-array copy, `.length=` rejection, and struct
  storage→storage copy. The interpreter's slot-level packed model is accurate on all of them.

Reproducers live in the scratchpad: `probe/src/Probe.sol`, `probe/src/Probe2.sol`,
`StructArr2.sol` / `FSA.sol` / `CDA.sol` (+ generated `*_witness.lean`).
