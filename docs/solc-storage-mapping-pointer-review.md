# solc storage mapping / nested-aggregate / pointer review (Fable)

Adversarial review of solidity-lean's storage **access-slot computation** for
mapping/nested/array types and **storage-pointer (local storage ref)** semantics
against pinned solc 0.8.35 (`/Users/dan/.solc-select/artifacts/solc-0.8.35`),
Forge `vm.load` ground truth, and the solc IR source
(`YulUtilFunctions.cpp`). Layout (packing/order/span) was already mined and
fixed (AGG1-3, DL1); this pass targets the ACCESS side: key preprocessing per
key type, nested-mapping recursion, array-of-struct spans, and pointer
aliasing/dangling.

**Verdict: CLEAN NEGATIVE.** Every slot formula and pointer behavior I checked
matches solc on deployed-contract ground truth. One low-confidence robustness
question (unforced `abiLazy` key) is documented but could not be reproduced —
the dominant paths force it correctly.

---

## What was verified against solc ground truth (all MATCH)

Probe contract deployed under pinned solc; each value written at a key, then
read back at the independently-computed slot via `vm.load`. All reads returned
the written sentinel → the Lean formula's preimage equals solc's.

| Key type | solc `h(key)` | slot check | Lean site | Result |
|---|---|---|---|---|
| `bytes` (dynamic) | raw bytes, no pad/len | `keccak(k ‖ pad32(p))` = written | `Interpreter.lean:1763-1767` | ✅ |
| `string` (dynamic) | raw bytes | `keccak(bytes(k) ‖ pad32(p))` | `1763-1767` (via `toCoreMappingKey?` → `bytesCalldata`, `Interface.lean:2242-2243`) | ✅ |
| `enum` | value padded32 | `keccak(pad32(2) ‖ pad32(p))` | `1780-1782` (enum → `uint256`, `Interface.lean:2245` + `toCoreStorageWord?` enum case) | ✅ |
| `bool` | `0/1` padded32 | `keccak(pad32(1) ‖ pad32(p))` | `1780-1782`; `coerceValue? bool` rejects non-0/1 (`386-394`) | ✅ |
| `int8 = -1` | **sign-extended** to `0xFF..FF` | `keccak(pad32(0xFF..FF) ‖ pad32(p))` | `1780-1782`; narrow ints carried full-width sign-extended (`Interface.lean:6942`) | ✅ |
| `int256 = -1` | `0xFF..FF` | same | `1780-1782` | ✅ |
| nested `m[a][b]` | recurse | `keccak(b ‖ keccak(a ‖ p))` | `State.resolveStoragePathSlot` mapping case, `4067-4069` + layout recursion | ✅ |

The dynamic-key formula matches solc's IR exactly: `mappingIndexAccessFunction`
(`YulUtilFunctions.cpp:2743-2755`) emits `dataSlot := <packedHash>(key, slot)`
for a dynamically-sized key = `keccak256(packed(key) . slot)`, packed = raw key
bytes; the fixed-key branch (`:2761-2774`) is `mstore(0,convertedKey);
mstore(0x20,slot); keccak256(0,0x40)` = `keccak(pad32(key) . pad32(slot))`. Lean
mirrors both (`mappingStorageSlot` at `1747-1748`, dynamic branch at
`1763-1766`). Key order (key first, slot second) matches.

The `int8 = -1` case is the one that could plausibly have diverged (truncated
`0xFF` vs sign-extended `0xFF..FF`): solc's `convertedKey =
conversionFunction(int8,int8)` sign-extends to full width, and solidity-lean
carries narrow signed values full-width (`Value.int` normalized to the 256-bit
two's-complement form, `Interpreter.lean:317-327,6942`), so `asStorageWord?`
yields `0xFF..FF`. Confirmed equal by `vm.load`.

## Storage pointers — aliasing & dangling (MATCH)

solidity-lean models a local storage ref as a **symbolic path**
`Value.storageRef name` / `Value.storagePathRef name indexValues`
(`Interpreter.lean:134-135`), where the index/key values are captured
(evaluated) at ref-creation time (`storageAliasPath`, `7959-7966`) and the slot
is **re-derived** from base-name + captured indexes on every read/write
(`resolveStoragePathSlot`, `4063-4090`). Because a mapping/array element slot is
a pure function of `(base slot, key)` — independent of array length or
liveness — re-derivation yields exactly the slot solc computed once. This makes
aliasing and post-mutation (dangling) behavior coincide with solc:

Deployed-solc ground truth (array of 2-slot `struct S{uint a,b}` at slot 0):
- `S storage r = arr[1]; arr.pop(); r.a` → **0** (pop zeroes the popped slots;
  ref still points at `keccak(0)+2`, reads the now-zero slot).
- `... arr.pop(); arr.push(S(9,10)); r.a` → **9** (slot reused; ref sees the new
  occupant).

The Lean path-ref reproduces both: `r` holds `("arr",[1])`, re-resolves to
`keccak(0)+1*span(2)` each access and reads live storage. The
`reference-mapping-storage` fixture already exercises delete-through-ref,
struct-ref rebind (`selected = other`), nested-mapping-ref, and
array/bytes dangling-after-delete, and is in the green 105/105 replay set.

## Layout spans touching access (MATCH)

`StorageLayout.slotSpan` (`1351-1369`): mapping / dynamicArray / bytes / string
each = 1 slot and force slot-alignment; struct = packed member span;
`fixedArray` of packed scalars = `ceil(size / floor(32/width))` (AGG3, no element
straddles a slot). Array-of-struct element slot =
`keccak(p) + index * span(struct)` (`dynamicArrayLayoutStorageSlot`,
`1794-1797`). Consistent with the already-fixed AGG3 span work and with the
struct/mapping placement in `cursorStep` (`1376-1411`).

---

## Low-confidence candidate (NOT reproduced) — unforced `abiLazy` mapping key

`mappingStorageSlotForKey` → `coerceMappingKeyWordAs` (`1750-1758`) coerces via
`Ty.coerceValue?` (which **preserves** an `abiLazy` wrapper, `386-389`) then
`Value.asStorageWord?`, which returns `none` for `Value.abiLazy` (`193-196`) →
`Except.error typeMismatch`. So an `abiLazy`-wrapped scalar key reaching this
function would **over-revert** where solc computes a slot.

In practice the dominant paths force the wrapper first: a bare narrow-int
parameter read goes through `derefMemoryValue`, which forces `abiLazy`
(`1085-1094`, `6149`), and array-index/byte-index keys use `expectWord`, which
also forces (`377-382`). This is confirmed clean by the
`abi-malformed` fixture (`mapping(uint8 => uint256) narrowMap;
narrowMap[seed] = seed;` with a `uint8` constructor param used directly as key —
`src/AbiMalformed.sol:152-156`), which is green.

I could not construct a path that delivers an **unforced** `abiLazy` scalar to
`mappingStorageSlotForKey` (e.g. a `uintN` calldata-array element used directly
as a key, `m[a[0]]`, without an intervening deref). If such a path exists it
would be an over-reject, not a wrong-slot. **Confidence this is a real
divergence: low (~15%).** Suggested probe if pursued: `mapping(uint8=>uint) m;
function f(uint8[] calldata a){ return m[a[0]]; }` with a clean element, replayed
through the interpreter — check for a spurious revert.

---

## Method notes
- Ground truth: scratch Foundry project, pinned solc 0.8.35, `optimizer=false`,
  `via_ir=false` (LEGACY, matching the corpus), `vm.load` at
  independently-`keccak256`-computed slots.
- solc IR cross-check: `YulUtilFunctions::mappingIndexAccessFunction`
  (`libsolidity/codegen/YulUtilFunctions.cpp:2739-2777`).
- Lean side read from `SolidCore/Solidity/Interpreter.lean` (slot math
  `1731-1836`, ref model `134-135, 4063-4090, 7955-8010`) and
  `SolidCore/Solidity/Interface.lean` (`toCoreMappingKey?` `2241-2245`,
  `toCoreStorageWord?` `2160-2237`).
- No Lean/semantics/fixture source was modified.
