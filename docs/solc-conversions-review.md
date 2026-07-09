# solc conversions review — ternary common-type & implicit conversions

Reviewer: Opus adversarial-review agent. Ground truth: pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`), verified with
`--ir`, `--bin`, and live execution on anvil. No semantics source modified.

## Summary

- **1 CONFIRMED wrong-value divergence** (TC1): ternary `? :` drops the implicit
  conversion of each branch to the conditional's common type. For `bytesN`
  branches of differing widths, the narrower branch is encoded at the wider width
  with **wrong byte alignment** (content lands in the low bytes instead of the
  high bytes). Affects return values, `abi.encode`, and `abi.encodePacked`.
- The integer conversion core (`uintCast?`/`intCast?`/`uintCleanup?`/`intCleanup?`,
  `Interpreter.lean:613-672`), address/bytesN masking, storage packed-int
  sign-extension, and the ternary *packing-width* type derivation
  (`Interface.lean:4932-4946`, `untypedLiteralMobileTy?`) were all audited and
  found to **match** solc. Only the branch-value conversion is missing.

---

## TC1 — ternary omits implicit branch→common-type conversion (bytesN misaligned)

**Severity: high (wrong value). Confidence: confirmed (live solc output).**

### Minimal repro
```solidity
// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
contract R {
    function f(bool c, bytes4 x, bytes2 y) external pure returns (bytes4) {
        return c ? x : y;                     // common type bytes4
    }
    function packed(bool c, bytes4 x, bytes2 y) external pure returns (bytes memory) {
        return abi.encodePacked(c ? x : y);
    }
    function enc(bool c, bytes4 x, bytes2 y) external pure returns (bytes memory) {
        return abi.encode(c ? x : y);
    }
}
```
Call with `c = false, x = 0x11223344, y = 0xaabb` (so the `y` branch is taken).

### What solc does (verified live on anvil + `--ir`)
solc's `TypeChecker::visit(Conditional)` computes the common type `bytes4` and
inserts `convert_t_bytes2_to_t_bytes4` on the `y` branch. In `--ir`:
```
expr_15 := convert_t_bytes2_to_t_bytes4(expr_14)
function convert_t_bytes2_to_t_bytes4(value) -> converted {
    converted := cleanup_t_bytes2(value)          // and(value, 0xffff00..00)
}
```
`bytesN` is **left-aligned** in solc's word repr, so `bytes2 0xaabb` widened to
`bytes4` keeps its content in the **high** bytes → `0xaabb0000`.

Live outputs (`cast call`, anvil, solc-0.8.35 runtime bytecode):
- `f`   → `0xaabb000000000000000000000000000000000000000000000000000000000000`
- `packed` payload (after offset+len 4) → `aabb0000`
- `enc` payload (after offset+len 32)  → `aabb0000...00`

### What Solidus does (wrong)
`Expr.ternary` is lowered by plain `Expr.toCore?`, which recurses into the
branches **without a target type** — no conversion is inserted:

- `SolidCore/Solidity/Interface.lean:4454-4459`
  ```
  | Expr.ternary cond thenExpr elseExpr => do
      let condCore ← Expr.toCore? storageNames cond
      let thenCore ← Expr.toCore? storageNames thenExpr
      let elseCore ← Expr.toCore? storageNames elseExpr
      some (Source.Expr.ternary condCore thenCore elseCore)
  ```
  (identical no-conversion recursion in the alias/annotate copies at
  `:202-203, :4932-4946` type side only, `:7101-7103`, etc.)

Solidus' internal `bytesN` convention is **right-aligned** (meaningful bytes in
the low position — see `Interpreter.lean:471`). The runtime ternary
(`Interpreter.lean:6591-6600`) returns the raw `y` branch value = internal
`0x0000aabb` and never widens it. The conditional's reported type is `bytes4`
(`Ty.commonImplicit?` bytesN case, `Interface.lean:3145-3148`), so the encoder
serialises a `bytes4` from that value:

- return / `abi.encode`: `abiStaticBytes?` `Ty.fixedBytes 4`
  (`Interpreter.lean:4513-4517`) → `wordToBytesBE 4 0x0000aabb ++ 28·0x00`
  = `0x0000aabb00…00`.
- `abi.encodePacked`: `abiEncodePackedValue?` `Ty.fixedBytes 4`
  (`Interpreter.lean:4993-4997`) → `wordToBytesBE 4 0x0000aabb` = `0000aabb`.

So Solidus yields `0x0000aabb…` everywhere solc yields `0xaabb0000…`.

### Classification
Wrong value (mis-encoded byte alignment). Reachable, differentially-live, and
almost certainly absent from the frozen corpus (needs a ternary of two
different-width `bytesN` operands — an uncommon shape).

### Root cause & fix direction (for the fix loop — not applied here)
The ternary branch lowering must convert each branch to the conditional's common
type, exactly as the array-literal path already does via
`Expr.toCoreAs? storageNames targetTy` (`Interface.lean:4776-4782`,
`arrayLiteralCoreExprsAs?`). For `bytesN` widening this inserts the
`fixedBytesCast M N` that shifts content from the low bytes to the high bytes
(`Interpreter.lean:591-601`), matching solc's `convert_t_bytesN_to_t_bytesM`.
Compute the common type with `Ty.commonImplicit?` on the two branch `abiTy?`s and
lower each branch with `toCoreAs?` that type.

Note: integer branches do **not** need this — narrow `intN`/`uintN` values are
stored already sign/zero-extended to full width (`intCast?` sign-extends,
`Interpreter.lean:639-655`), so widening is a no-op on the stored word. Only
`bytesN` (alignment-carrying) branches diverge. `fixed`/`ufixed` would too but are
out of the supported surface.

---

## Audited and MATCHING (no divergence found)

- **Integer narrowing/widening/reinterpret** — `uintCast?`/`intCast?`
  (`Interpreter.lean:613-655`): `uintN(x)` masks low `N` bits;
  `intN(x)` masks then sign-extends to full 256-bit stored form.
  `uint256(int8(-1)) = 2^256-1`, `int8(uint256(255)) = -1`,
  `int256(uint256 ≥ 2^255)` reinterpret — all correct. Narrow signed values are
  stored sign-extended, so mixed `uintN(intM)`/`intN(uintM)` and chained casts
  compose correctly.
- **Explicit conversions never revert** — truncation path (`uintCast`/`intCast`)
  is used for `Ty(x)`; the checked `*Cleanup?` variants are reserved for
  implicit-widening/literal validation. Matches solc (explicit casts truncate,
  never Panic).
- **address / bytesN masking** — `storageValueFromWord?`
  (`Interpreter.lean:460-475`): address read masks to 160 bits, `bytesN` read
  masks to the low `8N` bits (right-aligned convention); `address(uint160(x))`
  inserts `uintCast 160` (`Interface.lean:3819-3831`). Consistent with
  `cleanup_t_address` / `cleanup_from_storage_t_bytesN`.
- **bytesN↔bytesN / bytesN↔int explicit casts** — `fixedBytesCast?` truncates
  high→keeps-high and pads low with zeros in the right-aligned internal model,
  which reproduces solc's left-aligned `bytesN` truncation/extension
  (`Interpreter.lean:591-609`). `bytes20↔address` uses source-size 20 (identity).
- **ternary packing width for literals** — `untypedLiteralMobileTy?` +
  `Ty.commonImplicit?` (`Interface.lean:3474-3492, 3115-3168, 4932-4946`):
  `c ? 63 : 255` → uint8, `c ? uint16(300) : 5` → uint16,
  `c ? int16(-1) : -300` → int16, all match solc's `abi_encode_..._t_uintN`.
  `c ? 1 : -1` is **rejected** by solc ("uint8 does not match int8") and Solidus'
  `commonImplicit?` also returns `none` — consistent.
