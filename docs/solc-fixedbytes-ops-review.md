# solc vs Solidus — `bytesN` shift / bitwise-not lane-cleanup review

Surface: fixed-size byte operations (`bytesN << k`, `bytesN >> k`, `~bytesN`),
focusing on the interaction between Solidus's **right-aligned** internal `bytesN`
representation and solc's **left-aligned** representation with per-operation
cleanup. This surface was flagged as unmined; the frozen corpus only ever shifts
`uintN`/`uint256` values and then casts to `bytesN` (e.g. `bytes32(uint256(1) <<
200)` in `storage-dirty-words`, `abi-malformed`), never shifts/complements a
value *of `bytesN` type* and then observes it.

Ground truth: pinned solc 0.8.35 `--ir`.

## Root cause (shared by all findings)

solc stores `bytesN` **left-aligned** (meaningful bytes in the high-order bytes
of the word). Every `bytesN` shift and bitwise-not is compiled to *clean the
result back into the top-N-byte lane*:

```
function cleanup_t_bytes1(value) -> cleaned {
    cleaned := and(value, 0xff00…00)          // keep only the high byte
}
function shift_left_t_bytes1_t_uint8(value, bits) -> result {
    result := cleanup_t_bytes1(shl(bits, cleanup_t_bytes1(value)))
}
function shift_right_t_bytes1_t_uint8(value, bits) -> result {
    result := cleanup_t_bytes1(shr(bits, cleanup_t_bytes1(value)))
}
// ~b  ==>  cleanup_t_bytes1(not(b))
```

Solidus stores `bytesN` **right-aligned** (meaningful bytes low; left-alignment
happens only at the ABI boundary — see the storage-read comment at
`SolidCore/Solidity/Interpreter.lean:468-475`). Under that convention the
lane-cleanup obligation moves: `<<` and `~` are exactly the operations that push
bits **above** the N-byte lane, so they must be masked to `2^(8N)` afterward.
Solidus applies **no such mask**:

- Runtime `BinaryOp.applyWord` computes `shl` as a raw 256-bit
  `shlWord rhs lhs` — `SolidCore/Solidity/Interpreter.lean:5511`.
- Runtime `UnaryOp.apply` computes `~` as a raw 256-bit `notWord word` —
  `SolidCore/Solidity/Interpreter.lean:5658-5660`.
- The lowering-side cleanup helper `Ty.implicitCleanupCore?` inserts a
  truncating cast **only** for `Ty.uint`/`Ty.int` shift results; the
  `Ty.fixedBytes` case falls through to `| _ => some expr` with no mask —
  `SolidCore/Solidity/Interface.lean:3202-3232` (esp. the `| _ => some expr` at
  3232).
- `Expr.binaryToCoreWithEnvTyped?` returns `none` for `shl`/`shr`
  (`Interface.lean:6541-6542`), so shift operands lower through
  `coreAsFromTy? bytesN bytesN` → `implicitCleanupCore?` (no-op for `bytesN`) —
  `Interface.lean:6410-6413`. No lane mask is ever inserted anywhere.

The result: after `bytesN << k` or `~bytesN`, Solidus keeps dirty bits above the
byte lane. Those bits are dropped when the value is ABI-encoded/returned or
index-accessed (both take the low N bytes), so `return b << 4;` alone agrees
with solc. They become **observable** whenever the value is (a) compared
(`==`,`!=`,`<`,`>`,`<=`,`>=` compare the full 256-bit word), (b) fed into a
subsequent shift/bitwise op that brings the escaped bits back into the lane, or
(c) combined with `&`/`|`/`^`.

## Confirmed divergence 1 — `(b << 4) >> 4` on `bytes1` (wrong-value)

```solidity
function h(bytes1 b) external pure returns (bytes1) {
    return (b << 4) >> 4;
}
// call h(0xff)
```

- **solc:** `b<<4` = cleanup(shl(4, 0xFF00…0)) = `0xF000…0`; `>>4` =
  cleanup(shr(4, 0xF000…0)) = `0x0F00…0`. Returns **`0x0f`**.
  (IR verified: `shift_left_t_bytes1_t_uint8` / `shift_right_t_bytes1_t_uint8`
  both wrap in `cleanup_t_bytes1`.)
- **Solidus:** `b` = `0xff` (=255, right-aligned). `shlWord 4 255` = `4080`
  (`0xFF0`) — no lane mask. `shrWord 4 4080` = `255`. ABI-encodes low byte →
  returns **`0xff`**.
- **Classification:** wrong-value. **Confidence:** high (both sides verified —
  solc via `--ir`, Solidus by tracing `applyWord`/`shlWord`/`shrWord`).
- **Responsible:** missing lane cleanup after `bytesN <<`;
  `Interface.lean:3213-3232` (fixedBytes fall-through) + `Interpreter.lean:5511`.

## Confirmed divergence 2 — `(b << 4) == bytes1(0xf0)` (wrong-value / bool)

```solidity
function f(bytes1 b) external pure returns (bool) {
    return (b << 4) == bytes1(0xf0);   // call f(0xff)
}
```

- **solc:** `b<<4` cleans to `0xF000…0`; `bytes1(0xf0)` = `0xF000…0`; `eq` →
  **`true`**.
- **Solidus:** LHS `shlWord 4 255` = `4080`; RHS `bytes1(0xf0)` = `240`
  (right-aligned); `wordEq 4080 240` → **`false`**.
- **Classification:** wrong-value. **Confidence:** high.
- **Responsible:** same missing cleanup; comparison compares full words
  (`Interpreter.lean:5520`, `BinaryOp.eq => wordEq lhs rhs`).

## Confirmed divergence 3 — `(~b) == bytes1(0xf0)` on `bytes1` (wrong-value / bool)

```solidity
function n(bytes1 b) external pure returns (bool) {
    return (~b) == bytes1(0xf0);       // call n(0x0f)
}
```

- **solc:** `~b` = `cleanup_t_bytes1(not(0x0F00…0))` = `0xF000…0`; equals
  `bytes1(0xf0)` → **`true`**. (IR verified: `expr := cleanup_t_bytes1(not(...))`.)
- **Solidus:** `~b` = `notWord 15` = `0xFF…F0` (all high bits set, no lane mask);
  `wordEq (0xFF…F0) 240` → **`false`**.
- **Classification:** wrong-value. **Confidence:** high.
- **Responsible:** `UnaryOp.apply` `bitNot` returns bare `notWord`
  (`Interpreter.lean:5655-5660`); no `bytesN` lane cleanup in lowering
  (`Interface.lean:3213-3232`, unary path `Interface.lean:6292`).

## Notes / non-divergences (checked, agree with solc)

- `bytesN >> k` **alone** agrees (right-aligned `shrWord` drops low bits; no
  dirty high bits). e.g. `bytes1(0xff) >> 4` = `0x0f` on both.
- `return b << 4;` (encode/return path) agrees — `abiStaticBytes?`
  (`Interpreter.lean:4501`) takes the low N bytes, dropping escaped bits.
- `b[i]` index on a dirtied value agrees — `fixedBytesIndex?`
  (`Interpreter.lean:582`) reads via `wordToBytesBE size`, low N bytes.
- Event-topic encoding for indexed reference types was cross-checked against
  solc `ExpressionCompiler.cpp:986-994` (`packedEncode` + `KECCAK256`) and
  `ABIFunctions` `EncodingOptions` ("padded re-set to true for array/struct
  elements"): Solidus's `abiEventIndexedBytes?`/`abiEventTopic?`
  (`Interpreter.lean:4885-4930`) matches (raw bytes for top-level `string`/
  `bytes`, padded-per-element for arrays/tuples). No divergence found there.

## Suggested fix locus (for the loop, not applied here)

Insert a `bytesN`→`bytesN` lane truncation (a `fixedBytesCast size size` / mask
to `2^(8N)`) on the result of `bytesN <<` and `~bytesN` during lowering — the
natural home is `Ty.implicitCleanupCore?` (`Interface.lean:3202`) gaining a
`Ty.fixedBytes size` arm for the shift case, plus a mask on the unary-not
lowering; or mask in the runtime once the op knows it is operating on `bytesN`.
`>>`, index, and encode paths already agree and need no change.
