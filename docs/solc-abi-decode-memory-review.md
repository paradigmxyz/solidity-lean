# `abi.decode(bytes memory, (...))` — memory (eager) decode path review vs solc 0.8.35

Scope: the explicit `abi.decode` builtin on `bytes memory` (the EAGER memory
decoder), as distinct from the D1 calldata external-call boundary (lazy). Ground
truth: pinned solc 0.8.35 legacy codegen + Forge. Search-only; no semantics
changed.

## Where it lives in solidity-lean

- Memory decoder: `SolidCore/Solidity/Interpreter.lean:4839` `abiDecodeValueAtWithFuel?`
  (+ `abiDecodeValueAt?` :4949, `abiDecodeValues?` :4962). This is a *separate*
  function from the calldata boundary decoder (`ABI.lean:330`
  `decodeValueAtWithFuel?`), with no `lazy` flag and no
  `calldataDeferredInvalid` markers — i.e. genuinely eager, matching solc's
  `abi.decode`.
- Builtin lowering: `Interpreter.lean:6541` `Expr.abiDecode tys cleanups expr`.
  Flow: `value.asBytes?` → `abiDecodeValues? tys bytes` → on `none` revert EMPTY
  (`:6555`), on `some decoded` apply `AbiCleanups.acceptOrUnspecified cleanups`
  (revert EMPTY on reject, `:6554`), else return the value/tuple.
- Cleanup construction from the type list: `Interface.lean:5930` `Expr.toAbiDecode?`
  → `Tys.toCoreAbiCleanups?` → `Ty.toCoreAbiCleanup?` (`Interface.lean:2136`).

## Divergence found (1)

### D-MEM-1 — huge dynamic length reverts EMPTY instead of Panic(0x41)

Severity: wrong-revert-data (both revert; the returned revert data differs).
Confidence: 95%.

**Root cause.** solc's memory decoder for a dynamic array / `bytes` / `string`
*allocates the memory object before the tail bounds check*. `allocate_memory`
computes the new free pointer and reverts `Panic(0x41)` when it exceeds `2^64`.
So a length field large enough to overflow the allocation panics **0x41** —
regardless of whether the tail bytes are actually present. The solidity-lean
memory decoder never models allocation: `Ty.dynamicArray`
(`Interpreter.lean:4894`) and `Ty.bytesCalldata` (`:4889`) read the length, then
read elements/bytes one at a time; a length that outruns the data makes
`readWord?`/`readBytes?` return `none`, so `abiDecodeValues?` yields `none` and
the lowering reverts **EMPTY** at `Interpreter.lean:6555`. There is no
`Panic(0x41)` path in the memory-decode lowering at all.

**Trigger threshold (empirically pinned).** For `uint256[]` the panic begins at
`length ≥ 2^59` (2^59·32 = 2^64, the free-pointer overflow point); for `bytes`
at `length ≥ 2^64`. Below the threshold with insufficient data, both solc and
solidity-lean revert EMPTY (agree).

**solc evidence** (pinned solc 0.8.35, legacy, via `address(this).call`):

| input bytes (32-byte words)                    | decode type    | solc result            |
|------------------------------------------------|----------------|------------------------|
| `[0x20, 2^64, 0]`                              | `uint256[]`    | Panic(0x41) `..0041`   |
| `[0x20, 2^256-1]`                             | `uint256[]`    | Panic(0x41)            |
| `[0x20, 2^59, 0]`                             | `uint256[]`    | Panic(0x41)            |
| `[0x20, 2^58, 0]`                             | `uint256[]`    | REVERT_EMPTY           |
| `[0x20, 2^40, 0]`                             | `uint256[]`    | REVERT_EMPTY           |
| `[0x20, 2^64]`                                | `bytes`        | Panic(0x41)            |
| `[0x20, 1, 0x20, 2^64, 0]`                    | `uint256[][]`  | Panic(0x41) (inner)    |

**solidity-lean evidence** (`#eval abiDecodeValues? …`):

| input                                          | decode type    | solidity-lean result   |
|------------------------------------------------|----------------|------------------------|
| `[0x20, 2^64, 0]`                             | `uint256[]`    | `none` → revert EMPTY  |
| `[0x20, 2^256-1]`                            | `uint256[]`    | `none` → revert EMPTY  |
| `[0x20, 2^59, 0]`                            | `uint256[]`    | `none` → revert EMPTY  |
| `[0x20, 2^64]`                               | `bytes`        | `none` → revert EMPTY  |
| `[0x20, 1, 0x20, 2^64, 0]`                   | `uint256[][]`  | `none` → revert EMPTY  |

So on every huge-length shape solc returns `Panic(0x41)` while solidity-lean
returns the empty revert. Observable by any caller that distinguishes revert
kinds (`try/catch { Panic }`, inspecting bubbled revert data, `assertEq` on the
selector). Note there is no non-termination concern in the executable model: the
first out-of-data read short-circuits to `none`, so it never actually iterates
the huge count.

**Minimal repro (solc side):**

```solidity
function tryDecodeUintArr(bytes memory data) external pure returns (uint256) {
    uint256[] memory a = abi.decode(data, (uint256[]));
    return a.length;
}
// data = abi.encodePacked(uint256(0x20), uint256(2**59), uint256(0));
// solc: Panic(0x41);  solidity-lean: empty revert
```

**Fix sketch (not applied).** The memory-decode lowering (or the
`Ty.dynamicArray` / `Ty.bytesCalldata` cases of `abiDecodeValueAtWithFuel?`)
should compute the would-be allocation size and revert `Panic(0x41)` when it
overflows `2^64`, *before* the element/tail reads — mirroring solc's
`allocate_memory` ordering. Equivalent to a length guard: `uint256[N-byte-elem]`
panics when `length·elemStride + 0x20 > 2^64`; `bytes`/`string` panic when
`round32(length) + 0x20 > 2^64`.

## Clean negatives (checked, agree with solc)

1. **Basic / round-trip decode** — well-formed `[0x20,2,7,9]` → `uint256[]`
   decodes to `[7,9]`; value/tuple types decode correctly. Agree.
2. **Short / OOB / offset-OOB** — data shorter than the static head, an offset
   past end, a length exceeding remaining data (below the allocation threshold):
   both revert EMPTY. Agree. (`readWord?`/`readBytes?` bounds == solc's `end`
   check `revert(0,0)`.)
3. **Trailing extra bytes** — `abi.decode` ignores extra trailing data; the Lean
   decoder reads by index and imposes no exact-length check. Both accept. Agree.
4. **Dirty-bytes cleanliness (validate, not mask)** — the highlighted risk area,
   CLEAN:
   - `bool` (must be 0/1): validated inline in the decoder
     (`Interpreter.lean:4842`); dirty → EMPTY revert. Matches solc.
   - `address` (top 12 bytes zero): `abiAddressFits` inline (`:4848`). Matches.
   - `bytesN` (right padding zero): inline (`:4860`). Matches.
   - narrow `uintN`/`intN`, `enum`: decoded as full word, then rejected by the
     post-decode cleanup `AbiCleanups.acceptOrUnspecified` — `AbiCleanup.uint 8`
     rejects `0x1ff` (→ EMPTY revert), accepts `0xff`; verified vs solc
     `validator_revert_*` (dirty `uint8`/`bool` → EMPTY revert). Nested narrow
     ints inside arrays/structs are covered because `AbiCleanup.dynamicArray` /
     `.fixedArray` / `.tuple` recurse (`Interpreter.lean:334-339`,
     builder `Interface.lean:2151-2162`).
5. **Type-argument list** — `Ty.toCoreAbiCleanup?` maps every ABI value type to
   its validator (`uint/int/enum/array/tuple/struct`); mapping/fixed types are
   rejected (`none`), which is correct (not ABI types).

## Files / lines

- Memory decoder: `SolidCore/Solidity/Interpreter.lean:4839-4964`
  (dynamicArray `:4894`, bytesCalldata `:4889`, bool `:4842`, address `:4848`,
  bytesN `:4860`).
- Builtin lowering + revert wiring: `Interpreter.lean:6541-6556` (EMPTY revert
  on decode-`none` at `:6555`).
- Cleanup builder: `Interface.lean:2136-2173`, `5930-5938`.
- Calldata (lazy) counterpart for contrast: `ABI.lean:330-483`.
