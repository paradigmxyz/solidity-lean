# solc ABI decode-side validation review — nested/dynamic aggregate offset/length checks

Scope: the external-entry calldata decode path (public/external function params).
Focus: bounds/consistency validation of NESTED / DYNAMIC aggregates
(`bytes[]`, `T[][]`, structs with dynamic members, `T[2]`-of-dynamic).
Compiler ground truth: pinned solc 0.8.35 (`47b9dedd`) `--ir` + Forge execution.
solidity-lean: `SolidCore/Solidity/ABI.lean` decode path + `Interpreter.lean`.

Method: for each solc validator (`ABIFunctions.cpp` → `--ir` `abi_decode_*`),
compared the exact condition to solidity-lean's `decodeValueAtWithFuel?`
(`ABI.lean:319-431`) and the dispatch entry (`ABI.lean:676-708`). Malformed
calldata executed through solc-compiled bytecode via Forge (`staticcall` with
raw bytes).

## Summary

- **1 confirmed divergence** (over-reject / wrong-revert), with two concrete
  instances (`bytes[]` and struct-with-`bytes`). Both repros executed against
  the pinned binary: solc **accepts and returns a value**; solidity-lean
  **reverts empty**.
- Root cause is NEW and distinct from the already-mined S2 finding
  (`DECISIONS.md:3429`), which addressed *dirty-bit cleanup* timing
  (`abiLazy`/`memoryEager`). This finding is about *structural offset/length*
  validation timing for nested calldata dynamics — upstream of, and untouched
  by, the `abiLazy` cleanup machinery.
- The rest of the offset/length surface (top-level and structurally-reachable
  nested dynamics) is a **clean negative**: the drop-based relative-offset
  rebasing preserves the absolute end (`= calldatasize`) at every level and the
  per-word/`readBytes?` bounds match solc's `slt(add(offset,0x1f),end)` /
  `gt(add(arrayPos, mul(length,stride)), end)` checks exactly.

---

## D1 — Nested dynamic calldata elements are validated EAGERLY (over-reject)

**Classification:** over-reject / wrong-revert (solidity-lean `revert(0,0)`
where solc returns a value). **Confidence: high** (both sides executed /
source-traced).

### solc behavior (lazy: validate on access only)

For a calldata dynamic aggregate, solc's decode validates ONLY the immediate
structure and returns a calldata pointer; inner dynamic elements are validated
LAZILY when accessed.

`bytes[] calldata` decode (`--ir`, contract `N`):

```
function abi_decode_t_array$_t_bytes_calldata_ptr_$dyn_calldata_ptr(offset, end) -> arrayPos, length {
    if iszero(slt(add(offset, 0x1f), end)) { revert(...) }   // length word present
    length := calldataload(offset)
    if gt(length, 0xffffffffffffffff) { revert(...) }        // length <= 2^64-1
    arrayPos := add(offset, 0x20)
    if gt(add(arrayPos, mul(length, 0x20)), end) { revert(...) }  // HEAD area present
}
```

It never reads/validates any element's offset word or its `bytes`
length/data. `x[i]` access later runs `read_from_calldatat_...`
(`validator_revert_...`). Struct is even barer — `P{uint256 a; bytes b}`:

```
function abi_decode_t_struct$_P_$6_calldata_ptr(offset, end) -> value {
    if slt(sub(end, offset), 64) { revert(...) }   // 2 head words present
    value := offset                                // member b NEVER validated here
}
```

### solidity-lean behavior (eager: decode all elements at the boundary)

`decodeFunctionArgs?` (`ABI.lean:446`) → `decodeArgs?` (`:442`) →
`decodeValueAtWithFuel?`. The `dynamicArray` case (`ABI.lean:373-388`) and the
`tuple`-with-dynamic-members case (`:407-424`) EAGERLY materialize every
element via `decodeDynamicArrayValues?` / `decodeTupleValues?`. Each `bytes`
element runs the `bytesCalldata` case (`ABI.lean:368-372`):

```
let offset ← readWord? argData (wordBytes * headIndex)
let length ← readWord? argData offset
let bytes  ← readBytes? argData (offset + wordBytes) length
```

`bytes[]` lowers to `Ty.dynamicArray Ty.bytesCalldata`
(`Interface.lean:2085-2089`); the struct lowers to
`Ty.tuple [Ty.uint256, Ty.bytesCalldata]`. If ANY element's offset/length is
malformed, `readWord?`/`readBytes?` returns `none`, the whole
`decodeFunctionArgs?` returns `none`, and the dispatcher takes
`Contract.revertedEmptyCall?` (`ABI.lean:702`) → `revert(0,0)` — even when the
function body never touches the malformed element.

This is upstream of `abiLazy`: `abiLazy` only wraps a *successfully decoded*
scalar leaf to defer dirty-bit cleanup; it does not defer the structural
offset-resolution that fails here.

### Repro 1 — `bytes[]`, malformed unread element (executed, PASS = solc accepts)

Contract: `function f(bytes[] calldata x) external pure returns (uint256) { return x.length; }`

Calldata (`argData` after selector, headStart = 4):

| pos (in argData) | word | meaning |
|---|---|---|
| 0x00 | `0x20` | offset to array |
| 0x20 | `0x02` | array length = 2 |
| 0x40 | `0x40` | element0 offset (valid, → empty `bytes`) |
| 0x60 | `0xffffffffffffff00` | element1 offset — **garbage, < 2^64, never read** |
| 0x80 | `0x00` | element0 length = 0 |

- **solc:** decode passes (`arrayPos+2*0x20 = 0x84 <= calldatasize 0xa4`);
  `f` returns `x.length = 2`. **No revert.** (Forge `staticcall` → `ok=true`,
  return `2`.)
- **solidity-lean:** decoding element index 1 reads offset word
  `0xffffffffffffff00`, then `readWord? argData 0xffffffffffffff00` →
  `List.drop` past end → `none` → `revert(0,0)`.

### Repro 2 — calldata struct, malformed unread member (executed, PASS = solc accepts)

Contract: `struct P { uint256 a; bytes b; } function s(P calldata p) external pure returns (uint256) { return p.a; }`

Calldata:

| pos | word | meaning |
|---|---|---|
| 0x00 | `0x20` | offset to struct |
| 0x20 | `0x07` | `p.a = 7` |
| 0x40 | `0xffffffffffffff00` | `p.b` offset — **garbage, never read** |

- **solc:** `abi_decode_t_struct` only checks `end-offset >= 64`; `s` returns
  `p.a = 7`. **No revert.** (Forge → `ok=true`, return `7`.)
- **solidity-lean:** `decodeTupleValues?` eagerly decodes member `b`
  (`bytesCalldata`), reads offset `0xffffffffffffff00` → `none` → `revert(0,0)`.

### Impact / trigger surface

Any external/public function whose parameter is a **calldata** aggregate with
nested **dynamic** elements (`bytes[]`, `string[]`, `T[][]`, `bytes[N]`,
structs with dynamic members, and arrays/tuples thereof) AND whose body does
not access every element/member. Reading only `.length`, or only a subset of
elements, is the common trigger. Well-formed calldata is unaffected (eager and
lazy agree), which is why the happy-path corpus is green. The **memory**
counterpart matches solc (both eager — `memoryEager`, `DECISIONS.md:3429`); the
divergence is calldata-only, exactly where solc is lazy.

Note this is orthogonal to the mined narrow-int dirty-bit cleanup (S2): the
malformation here is a structural **offset**, not a dirty scalar, so neither
the `abiLazy` calldata-lazy path nor the `memoryEager` path addresses it.

---

## Clean negatives (verified faithful)

- **Top-level dynamic param bounds** (`bytes`, `T[]`): solidity-lean's
  `readWord? argData offset` requires `offset+32 <= argData.length`, matching
  solc `slt(add(offset,0x1f),end)`; `readBytes? argData (offset+32) length`
  requires `offset+32+length <= argData.length`, matching
  `gt(add(arrayPos, mul(length,stride)), end)`. `end = calldatasize` in both
  (solc threads outer `dataEnd`; solidity-lean's `argData = calldata.drop 4`).
- **Relative-offset base chaining for nested dynamics:** solidity-lean rebases
  to `argData.drop (offset+wordBytes)` for arrays (`ABI.lean:381`) and
  `argData.drop offset` for tuples/fixed-arrays-of-dynamic (`:400,:419`). Since
  `List.drop` preserves the tail, the absolute end stays `calldatasize` at every
  level — identical to solc threading a constant `dataEnd`. Backward-pointing
  offsets are impossible in both (unsigned add from base); overlapping/forward
  offsets accepted by both.
- **`length <= 2^64-1` / offset `<= 2^64-1`:** not separately checked by
  solidity-lean, but functionally subsumed — any out-of-range value makes the
  subsequent `readWord?/readBytes?` fail (`List.drop` of a huge index = `[]`),
  producing the same revert. No over-accept.
- **`bytes[N]` (fixed array of dynamic) and `T[][]` reachable elements:** base
  = `argData.drop offset` (no length prefix for the fixed array), element heads
  read relative to it — matches solc's `dataPtr = headStart+offset` with no
  length word. Structurally-accessed elements validate identically.
- **Value-type array element cleanup (uint8[]/bool[]/address[] calldata):**
  lazy-on-access in both (solidity-lean `abiLazy` via `lazyValues`
  `Interpreter.lean:5185`; solc `read_from_calldata...` + validator). Faithful
  (already mined S2).
- **Trailing data:** both allow extra bytes past the consumed region at the
  outer tuple; neither validates `bytes` padding bytes.

---

## Repro artifacts

Foundry project (pinned solc 0.8.35, optimizer off): both tests PASS, i.e. solc
accepts calldata that solidity-lean's source rejects.

- `f(bytes[])` — `test_malformed_unread_element` → `ok=1`, `length=2`.
- `s((uint256,bytes))` — `test_struct_malformed_unread_member` → `ok=1`, `a=7`.
