# WS3 — EVM-faithful calldata tail-pointer wrap (#129 CALLDATA-TAIL-WRAP)

## 1. The exact EVM/solc rule (confirmed from source + on-chain)

Two *different* offset-validation regimes exist in solc 0.8.35's ABI decoder,
and the divergence lives in the difference between them.

### 1a. EAGER (memory-location) decode — UNSIGNED, reverts. (matrix owner — DO NOT TOUCH)
The top-level tuple decoder and the memory array/struct decoders validate every
tail offset with an UNSIGNED `gt`/`slt`-of-remaining check and revert on OOB:

- `ABIFunctions::tupleDecoder` (libsolidity/codegen/ABIFunctions.cpp:235-242):
  ```
  let offset := calldataload(add(headStart, <pos>))
  if gt(offset, 0xffffffffffffffff) { revert }        // rejects any high-bit offset
  <values> := <abiDecode>(add(headStart, offset), dataEnd)
  ```
- `abiDecodingFunctionArrayAvailableLength` (…:1168-1234) — memory array element:
  ```
  let srcEnd := add(offset, mul(length, <stride>))
  if gt(srcEnd, end) { revert }                        // unsigned OOB → revert
  let innerOffset := <load>(src)
  if gt(innerOffset, 0xffffffffffffffff) { revert }
  ```
- `abiDecodingFunctionCalldataArray` (…:1226-1266) — length/stride guards, all `gt`.

Because a top-level dynamic param offset is rejected once it exceeds
`0xffffffffffffffff` (2^64-1, NOT high-bit), **top-level params CANNOT wrap.**
The model mirrors this eager path via `readWord?`/`readBytes?` returning `none`
(= empty revert) on OOB, plus `abiCheckAllocation?` for Panic(0x41). This is the
96/96 malformed-revert matrix (#22/#41/#101/#124/#128). **Unchanged by WS3.**

### 1b. LAZY (calldata-location) nested tail access — SIGNED, WRAPS. (the divergence)
When a *calldata* aggregate of *dynamic* elements is accessed element-by-element
at runtime (`bytes[] calldata a; … a[i]`, or a calldata struct's dynamic member),
solc emits `access_calldata_tail` (YulUtilFunctions.cpp:2541-2568):

```
function access_calldata_tail(base_ref, ptr_to_tail) -> addr, length {
    let rel_offset_of_tail := calldataload(ptr_to_tail)
    if iszero(slt(rel_offset_of_tail,
                  sub(sub(calldatasize(), base_ref), sub(<neededLength>, 1)))) { revert }  // SIGNED
    addr := add(base_ref, rel_offset_of_tail)          // WRAPS mod 2^256
    length := calldataload(addr)                        // zero-padded past calldatasize
    if gt(length, 0xffffffffffffffff) { revert }
    addr := add(addr, 32)
    if sgt(addr, sub(calldatasize(), mul(length, <calldataStride>))) { revert }  // SIGNED
}
```
(`calldataAccessFunction`, ABIFunctions.cpp:1432-1477, is the equivalent used
inside calldata-array→memory copies and struct member reads.)

The `slt` is a **signed** comparison. A `rel_offset_of_tail` with bit 255 set is
NEGATIVE in signed interpretation, so `slt(neg, positive_RHS)` is TRUE and the
check PASSES. Then `add(base_ref, rel_offset)` computes `base_ref + rel_offset`
**mod 2^256** and wraps around. `neededLength` = the element type's
`calldataEncodedTailSize` (32 for `bytes`/`string`/`T[]`).

## 2. On-chain verification (pinned solc 0.8.35, Forge 1.5.1)

Contract `Wrap2 { function f(bytes[] calldata a) external pure returns (bytes memory) { return a[0]; } }`
Hand-crafted calldata via low-level `staticcall` (the model's own encoder never
emits a high-bit offset — this case is only reachable adversarially). Positions
are absolute calldata bytes; `headStart = 4`, `base_ref = arrayPos = 164`,
`calldatasize = 196`, element neededLength = 0x20, stride = 1.

| case | elem head rel_offset | EVM result | why |
|---|---|---|---|
| **wrap-success** | `2^256-128` (= -128) | **ok, returns `0xaabb`** | slt(-128, 196-164-31=1)=T → passes; addr=164-128=36; length=calldataload(36)=2; data at 68 = `0xaabb` |
| wrap-far | `2^255` | ok, returns `0x` (empty) | slt passes; addr huge; calldataload→0 → length 0; `sgt(addr+32, csz)` signed sees NEGATIVE addr → no revert → empty bytes |
| pos-OOB | `0x1000` | **revert (empty)** | slt(0x1000, 1)=F → `iszero`→revert |
| normal-fwd | `0x20` | ok, returns `0xaabb` | ordinary in-bounds forward tail |

`ret` for the two success bytes cases is the ABI encoding of `bytes` (offset
0x20, length, data). Commands: `forge test` in `scratchpad/wrap-evm-probe`
(self-contained, no forge-std; low-level staticcall with `abi.encodePacked`
calldata). Reproduced verbatim in the WS3 Forge lane below.

## 3. The model's current rule and where it diverges

`SolidCore/Solidity/ABI.lean :: decodeValueAtWithFuel?` decodes over `Ty` using
**`.drop`-relative Nat positions**: each nested value is decoded by passing
`argData.drop <somePos>` and re-basing to word index 0, with every tail offset
read as a plain `Nat` and every read via `readWord?`/`readBytes?` that returns
`none` (→ empty revert) when the position is past the (finite) `argData`.

On the LAZY (calldata) path, when a nested dynamic element's tail read fails —
which is exactly what a high-bit offset triggers, since `argData.drop hugeOffset`
is `[]` and `readWord?` yields `none` — the aggregate arms
(`decodeDynamicArrayValues?` :447-464, `decodeArrayValues?` :498-508,
`decodeTupleValues?` :541-553) substitute a `Value.calldataDeferredInvalid`
marker (Interpreter.lean:427: `abiLazy (AbiCleanup.uint 0) ty.defaultValue`) that
**reverts empty on ACCESS**.

Divergence: the model **always reverts** (marker) on a high-bit nested tail
offset; the EVM **wraps mod 2^256** and, for a crafted value, reads a valid
in-bounds region and **succeeds with real bytes** (`0xaabb`). Three root causes:
1. The comparison is effectively UNSIGNED-via-bounds (`readWord?` none on OOB),
   not the EVM's SIGNED `slt` — so a "negative" offset is wrongly rejected.
2. Positions are `.drop`-relative, so there is no absolute `base_ref` to add the
   offset to, and no mod-2^256 wrap — an offset can only ever move forward.
3. Reads REVERT past `argData.length`; the EVM `calldataload` ZERO-PADS, and the
   subsequent signed stride check (not a read-failure) is what decides revert.

Note the selector-coordinate shift: model `argData = calldata.drop 4`, so model
pos = EVM pos − 4. In the `slt` RHS the two `+4`s cancel
(`csz − base_ref = (argData.length+4) − (model_base+4) = argData.length − model_base`),
but the `add(base_ref, rel_offset)` wrap and the final `sgt` compare *absolute*
256-bit values, so a faithful model must carry the `+4` (or equivalently compute
in EVM-absolute coordinates and translate back by −4 for the actual byte read).
A wrap that lands in the selector region (EVM addr ∈ [0,3]) is unrepresentable in
`argData` and is a documented residual (adversarial, never a real payload).

## 4. Representation / boundary change (Stage B)

Scope: the **lazy** nested-dynamic-element tail access ONLY. The eager path
(matrix owner) is untouched.

The clean, compositional reformulation carries an **absolute EVM-coordinate base**
instead of `.drop`-relative Nat, and follows a dynamic calldata element's tail via
an EVM-faithful primitive `accessCalldataTail?`:

```
-- csz = argData.length + 4 (EVM calldatasize); baseEvm = model_base + 4.
-- signed256 x = if x ≥ 2^255 then (x : Int) - 2^256 else x
-- readWordZeroPad argData p = bytesToWordBE of calldata[p..p+32], zero past csz
def accessCalldataTail? (argData) (baseEvm relSlotEvm neededLen stride) :
    Except RevertData (Nat × Nat) :=            -- (addrEvm, length)
  let rel := readWordZeroPad argData relSlotEvm      -- rel offset word
  if ¬ signed256 rel < (csz - baseEvm - (neededLen - 1) : Int) then error empty
  let addr := (baseEvm + rel) % 2^256
  let length := readWordZeroPad argData addr
  if length > 2^64 - 1 then error empty
  let addr2 := (addr + 32) % 2^256
  if signed256 addr2 > (csz - length*stride : Int) then error empty
  ok (addr2, length)
```

Then a dynamic calldata element is decoded by reading its bytes at
`calldata[addr2 .. addr2+length]` (translating EVM→model coord by −4, zero-pad),
recursing with the same primitive for nested dynamics. Only DYNAMIC elements use
this (mirrors solc: `access_calldata_tail` is only generated for dynamic base
types); a *static* dirty element keeps the deferred marker (solc validates it on
access via `validator_*`, which reverts — the marker's existing behavior is
already faithful there).

Blast radius: within ABI.lean, the lazy arms of `decodeValueAtWithFuel?`
(dynamicArray/fixedArray-of-dynamic/tuple-with-dynamic element loops) route a
dynamic element through `accessCalldataTail?` + a wrapped byte read instead of
`.drop`-relative decode-or-marker. Value-type and eager paths unchanged.
`decodeValueAtWithFuel?` is referenced ONLY in ABI.lean and appears in NO proof
file (FuelMonotonicity/AdoptionLaws are about `eval`), so no proof change is
expected; the decode fuel measure is preserved by keeping the recursion shape.

## 5. Faithfulness target

MUST now succeed (was: revert on access):
- `f(bytes[] calldata a) returns(bytes){ return a[0]; }` with the wrap calldata of
  §2 → returns `0xaabb`. Witness pins the decoded `Value.bytes [0xaa,0xbb]`.
- wrap-far offset `2^255` → returns empty bytes (length 0).

MUST still revert with the EXACT kind (regression armor — eager matrix):
- truncated dynamic-element-array head (memory param) → EMPTY (#128), not Panic.
- oversized eager `bytes`/array length (memory param) → Panic(0x41) (#41).
- array element OOB access → Panic(0x32).
- pos-OOB nested tail offset (`0x1000`, calldata param) → EMPTY revert.
- top-level dynamic param offset > 2^64-1 → EMPTY revert (unsigned, no wrap).

## 6. Status / recommendation

Ground truth fully confirmed (source + on-chain). This is the architectural item
the memory log flags as user-pending #129: it is a *representation* change to the
decoder (absolute EVM-coordinate positions + signed/mod-2^256/zero-pad on the lazy
path), not a compositional one-liner, and it is NOT replay-reachable (the model's
encoder never emits high-bit offsets; only hand-crafted calldata hits it). The
eager malformed matrix and all proofs are isolated from the change, so it is
tractable and bounded to ABI.lean's lazy arms.
