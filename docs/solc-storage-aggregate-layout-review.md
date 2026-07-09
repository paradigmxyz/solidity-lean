# Divergence review: storage layout of structs, nested aggregates, and mapping keys (solc 0.8.35 vs solidity-lean)

Round target: the storage-layout **re-derivation surface** for struct field
packing, nested aggregates, and mapping-key hashing — distinct from
inheritance slot ORDER (DL1, fixed) and from array-of-value-type element
packing (bug-batch #1, in flight). solc source: `/Users/dan/Projects/solidity-src`
@ 0.8.35 (47b9dedd), read-only. Probes: pinned
`~/.solc-select/artifacts/solc-0.8.35/solc-0.8.35 --combined-json storage-layout`
and a Forge `vm.load` suite (no solidity-lean build/run; Lean side is code audit).

## Executive summary

Surfaces read: solidity-lean's entire storage-layout re-derivation pipeline —
`Ty.toCoreStorageLayout?` / `Ty.toCoreStorageMemberLayout?` /
`Tys.toCorePackedStorageLayouts?` / `CoreStorageLayout.placeInPackedCursor`
(`SolidCore/Solidity/Interface.lean:2160-2350`), top-level
`ContractDecl.storageFieldAndNext` (`Interface.lean:18431-18469`), the
runtime replay `StorageLayout.slotSpan` / `cursorStep` /
`fieldOffsetAndLayout?` / `arrayElementOffsetAndLayout?`
(`SolidCore/Solidity/Interpreter.lean:1322-1464`), the slot algebra
(`Interpreter.lean:1716-1809`), and the aggregate load/store walkers
(`Interpreter.lean:3091-3260`, `3760-4030`). solc's concrete rules:
`StorageOffsets::computeOffsets` (`libsolidity/ast/Types.cpp:142-175`),
`ArrayType::storageSize` (`Types.cpp:1818-1836`), `StructType::storageSize`
(`Types.cpp:2322`), per-type `storageBytes`/`leftAligned` (`Types.h:286-293,
459-460, 505-506, 701-702, 729-730, 978-979`), and
`YulUtilFunctions::mappingIndexAccessFunction` / `packedHashFunction`
(`libsolidity/codegen/YulUtilFunctions.cpp:2739-2777, 4113-4145`).

**NEW findings: 2 differentially-live SOUNDNESS findings (both CONFIRMED),
plus 1 IN-FLIGHT-RELATED confirmation.** Ranked:

1. **AGG1 (SOUNDNESS, wrong-slot, CONFIRMED, DIFFERENTIALLY-LIVE)** —
   `mapping(bytesN => V)` keys (N = 1..31) are hashed **right-aligned**;
   solc hashes the **left-aligned** stack form. Every entry of such a
   mapping lands at the wrong storage slot.
2. **AGG2 (SOUNDNESS, wrong-slot / wrong-span, CONFIRMED,
   DIFFERENTIALLY-LIVE)** — contract-typed storage members have **no
   storage lowering at all**: a contract-typed state variable never packs
   (solc packs it as a 20-byte value), a struct containing a contract-typed
   field gets `layout? = none` (span collapses to 1 slot and field access
   falls back to the non-keccak `legacyIndexedStorageSlot` FNV path), and
   `mapping(ContractType => V)` uses the FNV path instead of
   `keccak256(pad(addr) . slot)`.
3. **AGG3 (IN-FLIGHT-RELATED)** — the fixed-array slot span
   `natCeilDiv(size * widthBytes, 32)` lets elements straddle slots; solc
   uses `ceil(len / floor(32/width))` (`uint40[32]`: solc 6 slots, solidity-lean
   5), so the state variable / struct field *after* such an array sits one
   or more slots too low. Same root cause as bug-batch #1 (array element
   packing); recorded here because the **span** consumers
   (`placeInPackedCursor`, `storageFieldAndNext`) also need the fix.

Everything else on the target list is **FAITHFUL** (probe-verified on the
solc side, code-audited on the solidity-lean side): struct field packing
including the doesn't-fit-starts-new-slot rule and the 31+1-byte boundary,
nested-struct whole-slot alignment, struct total-span rounding, aggregate
members (fixed/dynamic array, mapping, bytes/string) aligning to fresh
slots inside structs, struct-in-array stride, `bytes`/`string` mapping keys
hashed as **raw unpadded bytes** (including the empty key), signed /
address / bool / enum / uint keys padded to 32 bytes (signed keys
sign-extended), and nested-mapping hash composition.

## Mapping-key-hashing verdict (explicit)

solc computes the value slot as `keccak256(h(key) . uint256(slot))`
(`mappingIndexAccessFunction`, YulUtilFunctions.cpp:2739-2777):

- **value-type key**: `h(key)` = the *cleaned stack form* stored as one
  32-byte word (`mstore(0, <convertedKey>)`), i.e. right-aligned
  zero/sign-extended for uintN/intN/bool/address/enum/contract, but
  **LEFT-aligned** for `bytesN` (`FixedBytesType::leftAligned = true`,
  Types.h:702);
- **`bytes`/`string` key**: `h(key)` = the **raw key bytes, unpadded**,
  with the slot appended as a full word (`packedHashFunction` →
  `tupleEncoderPacked`, YulUtilFunctions.cpp:4113-4145).

solidity-lean (`mappingStorageSlotForKey`, Interpreter.lean:1745-1755):

- `bytes`/`string` keys → `keccak(rawBytes ++ word(slot))` — **FAITHFUL**
  (verdict: value-key vs bytes/string-key *distinction* is correctly
  modeled; probe `testBytesStringKey` confirms solc side, incl. empty key
  = `keccak(slot)` and that the ABI-padded variant does NOT match).
- value-type keys → `keccak(word(key) ++ word(slot))` where `word(key)` is
  the internal **right-aligned** word — FAITHFUL for
  uint/int/bool/address/enum (int keys are full-word two's complement,
  `intCast?` Interpreter.lean:639-655, matching solc's sign-extension;
  Forge probe `testInt8Key*`: only the sign-extended slot holds the
  value), but **WRONG for `bytesN` keys** (AGG1) and **unreached for
  contract-type keys** (AGG2c).

## Findings

### AGG1 — `mapping(bytesN => V)` key hashed right-aligned (solc: left-aligned)

- **solc evidence.** `mappingIndexAccessFunction` stores the *converted
  stack value* of the key at memory 0 (YulUtilFunctions.cpp:2762-2775);
  bytesN stack values are left-aligned (Types.h:701-702). Forge probe
  (`testBytes4Key`, `testCtrBoolNest`): after `mb4[0xaabbccdd] = 111`,
  `vm.load(keccak256(abi.encode(bytes32(bytes4(0xaabbccdd)), slot)))`
  = 111 while the right-aligned preimage slot
  (`abi.encode(uint(0xaabbccdd), slot)`) is 0. Same for the nested
  `mnest[7][0xaabbccdd]` inner/outer composition.
- **solidity-lean status.** `Ty.toCoreMappingKey?` (Interface.lean:2232-2236)
  lowers a bytesN key to core `fixedBytes n`;
  `mappingStorageSlotForKey` → `coerceMappingKeyWordAs`
  (Interpreter.lean:1735-1755) coerces (`Ty.fixedBytes _, Value.word v =>
  v`, Interpreter.lean:399) and serializes with `storageWordBytes` — the
  documented **right-aligned** internal bytesN convention
  (Interpreter.lean:468-475). Preimage word is right-aligned → wrong slot
  for every N in 1..31 (N = 32 coincides). UDVT-over-bytesN keys resolve to
  `fixedBytes` (`Ty.resolveUserTypes`, Interface.lean:824-845) and inherit
  the bug.
- **Severity / confidence / reachability.** SOUNDNESS (wrong-slot → wrong
  observed-storage word, and wrong value if the entrant probes solc's
  slot). CONFIRMED (solc probe + unambiguous solidity-lean code path).
  DIFFERENTIALLY-LIVE: the harness's §3.4 component 5 compares
  entrant-declared raw slots (`contest/observable.py:131-150`,
  `contest/adjudicate.py:498`), and `bytesN` mapping keys pass the
  acceptance gate (`Ty.isMappingKeyShape`, TypeCheck.lean:459-473).
- **Fix sketch.** In `mappingStorageSlotForKey`, shift bytesN keys left
  before hashing: preimage word = `key << (8*(32-n))` (key type must carry
  `n`; core `fixedBytes n` already does).

### AGG2 — contract-typed storage members have no storage lowering

Root cause: `Ty.toCoreStorageWord?` (Interface.lean:2160-2189) and
`Ty.storagePackedBytes?` (Interface.lean:2191-2221) have **no `Ty.user`
case**, and no resolution pass rewrites contract types to `address`
(importer emits `Ty.user`, `scripts/solc_ast_to_lean_source.py:619-623`;
`resolveUserTypes`/`resolveEnums`/`resolveStructs` cover only
UDVTs/enums/structs). solc: `ContractType::storageBytes() = 20`
(Types.h:978), packed like an address by
`StorageOffsets::computeOffsets` (Types.cpp:142-175).

Three concrete sub-surfaces (all accepted by the gate —
`isValueTypeShape`/`isMappingKeyShape` include `isContractValuePath`,
TypeCheck.lean:432-473; `StateVarDecl.check` TypeCheck.lean:9353-9410 adds
no storage-lowering requirement; no `contest/known_gaps.py` entry):

- **AGG2a — top-level state variable never packs.** In
  `ContractDecl.storageFieldAndNext` (Interface.lean:18431-18469) a
  contract-typed var takes the `_, _` fallback: full aligned slot, span 1,
  `layout? = ty? = none`. Probe (`Layout2.sol`): solc gives
  `uint96 u @0+0; IERC20 c @0+12; uint8 z @1+0` — solidity-lean places `c` at
  slot 1 and `z` at slot 2. Wrong slot for the contract var **and every
  subsequent variable** (including inherited-layout bases via
  `storageFieldsSlotSpanFrom`, Interface.lean:18488-18493). Also applies
  to the transient lane (contract-typed transient vars pass the value-type
  gate, TypeCheck.lean:9398-9402). Conversely, when the contract var
  starts a fresh slot and the *next* var is ≤ 12 bytes, solc packs it into
  the same slot (probe `Layout.sol`: `c0 @19+0` alone only because
  `address a0` doesn't fit; a following `uint96` would pack) — solidity-lean
  never does.
- **AGG2b — struct with a contract-typed field: whole struct layout
  vanishes.** `Ty.toCoreStorageMemberLayout?` → `Ty.toCoreStorageLayout?`
  returns `none` for the field, so the **entire struct's** layout is
  `none` (Interface.lean:2281-2283, 2330-2341). Consequences: (i) span
  collapses to 1 (`| none => 1`, Interface.lean:18463) — solc's
  `struct S { IERC20 t; uint256 x; }` spans 2 slots (probe: members
  `t@0+0, x@1+0`, following var at slot 4 vs solidity-lean slot 3); (ii) member
  access falls to the layout-less fallback, `legacyIndexedStorageSlot slot
  * 16777619 + key + 1` (Interpreter.lean:1803-1806; used at 3857-3864,
  3977-3983, 4183, 4259) — not keccak-based at all, so *every field* of
  such a struct lives at a slot unrelated to solc's; (iii) solc packs
  contract fields inside structs (probe: `struct WithCtr { IERC20 t;
  uint96 y; }` → `t@0+0, y@0+20`, 32 bytes total). Same collapse for
  `IERC20[k]` / `IERC20[]` members and for mappings *valued* in such
  structs.
- **AGG2c — `mapping(ContractType => V)` uses the FNV fallback.**
  `Ty.toCoreMappingKey?` → `Ty.toCoreStorageWord?` = none → the mapping's
  layout is `none` → `m[k]` reads/writes at `legacyIndexedStorageSlot`
  (Interpreter.lean:4183, 4259) instead of solc's
  `keccak256(pad32(addr) . slot)` (Forge probe `testCtrBoolNest`: padded
  address preimage holds the value).
- **Severity / confidence / reachability.** SOUNDNESS (wrong-slot →
  wrong observed-storage values; AGG2b additionally shifts every later
  state variable). CONFIRMED (solc probes above + unambiguous Lean code
  path; solidity-lean not executed — the only step short of full confirmation is
  replaying a Lean example, blocked by the read-only constraint).
  DIFFERENTIALLY-LIVE (contract-typed state vars/keys are ubiquitous
  Solidity and pass both solc and the solidity-lean gate).
- **Fix sketch.** Give `Ty.user` (contract paths) the address lowering in
  `Ty.toCoreStorageWord?` (→ `Ty.address`) and `Ty.storagePackedBytes?`
  (→ 20), or rewrite contract-typed *storage* types to `Ty.address` in a
  resolution pass; then AGG2a-c all collapse into the existing
  address-typed machinery. Consider afterwards whether
  `legacyIndexedStorageSlot` has any remaining legitimate caller — every
  `layout? = none` runtime path is a divergence by construction.

### AGG3 — fixed-array slot span straddles slots (IN-FLIGHT-RELATED)

- **solc evidence.** `ArrayType::storageSize` (Types.cpp:1818-1836):
  `itemsPerSlot = 32 / baseBytes` (floor), `size = ceil(len /
  itemsPerSlot)`; elements never straddle a slot
  (`ArrayType::storageStride`, Types.h:901). Probe: `uint40[32] f1` at
  slot 25 spans **6** slots (`numberOfBytes = 192`), `uint8 tail1 @31`.
- **solidity-lean status.** `StorageLayout.slotSpan` for
  `fixedArray size (packedScalar _ w _ _)` = `natCeilDiv (size * w) 32`
  (Interpreter.lean:1355-1357, also 1395-1399) → 5 slots for `uint40[32]`;
  `arrayElementOffsetAndLayout?` (Interpreter.lean:1450-1464) places
  element i at byte `i*w`, straddling slot boundaries. Consumed by
  `placeInPackedCursor` (Interface.lean:2267-2271) and
  `storageFieldAndNext` (Interface.lean:18459-18462), so a struct field or
  state variable *after* such an array lands too low (probe: `tail1` slot
  31 vs solidity-lean 30).
- **Status.** The element-packing half is bug-batch #1 (IN-FLIGHT, sibling
  agent). Recorded here only to flag that the **span formula and both its
  layout-cursor consumers** must change together
  (`ceil(size / (32 / w))`, element i at slot `i / (32/w)`, offset
  `(i % (32/w)) * w`) — fixing element access without the span leaves
  every post-array field one-plus slots off. Not counted as NEW.

## Faithful surfaces (probe- and code-verified this round)

solidity-lean's packing cursor (`placeInPackedCursor`, Interface.lean:2249-2271)
is the same algorithm as `StorageOffsets::computeOffsets`
(Types.cpp:142-175): fit-check `offset + width <= 32` (solc:
`byteOffset + storageBytes > 32` → next slot), never splitting a value
across slots, aggregates aligned to a fresh slot with the *next* member
also slot-aligned, and end-of-struct round-up (`finishSlot` ↔ solc's
trailing `if (byteOffset > 0) ++slotOffset`). The runtime replay
(`cursorStep`, Interpreter.lean:1370-1403; `fieldOffsetAndLayout?`,
:1432-1448) re-derives slots from the recorded packed offsets with the
`offset < cursor.offset → new slot` rule, which is consistent-by-
construction with the packer (audited: fits / doesn't-fit / lane-full /
aggregate-align cases all replay to the same slots).

Verified against `--combined-json storage-layout` (`Layout.sol` probe):

| case | solc | solidity-lean | verdict |
|---|---|---|---|
| `{uint128; uint64; uint64}` | a@0+0, b@0+16, c@0+24; 1 slot | same | FAITHFUL |
| `{uint128; uint128; uint8}` (doesn't fit → new slot) | c@1+0; 2 slots | same | FAITHFUL |
| `{uint248; uint8; uint8}` (31+1 boundary) | a@0+0, c@0+31, d@1+0 | same | FAITHFUL |
| nested struct `{uint8; Inner{uint8}; uint8}` | a@0, i@1, b@2 (no cross-boundary packing) | same (`align` + whole-slot span) | FAITHFUL |
| `uint8[3]` field between uint8s | arr@1, b@2 | same (array member aligns, next field new slot) | FAITHFUL |
| dyn-array / mapping / bytes members in struct | 1 aligned slot each; next field new slot | same | FAITHFUL |
| struct span used as array stride (`Pack3[]`, `Pack3[2]`) | 1-slot stride; fixed = 2 slots | `slotSpan` = packed-cursor span | FAITHFUL |
| `uint8[33]` | 2 slots, next var after | `natCeilDiv(33,32)=2` | FAITHFUL (width divides 32) |
| enum fields/vars | 1 byte, packs (`EnumType::storageBytes`, Types.cpp:2653-2657; ≤256 members asserted) | `packedScalar 0 1` | FAITHFUL |
| external / internal fn-ptr storage width | 24 / 8 (`FunctionType::storageBytes`, Types.cpp:3294-3301) | 24 / 8 (Interface.lean:2217-2220) | FAITHFUL |
| packed lane bit position | offset from least-significant byte; bytesN low-aligned *in storage* | `wordBitRange (offset*8)` (Interpreter.lean:3098-3100, 3204-3210); right-aligned bytesN convention (:468-475) | FAITHFUL |

Verified against the Forge probe (mapping keys) and code audit:

| case | solc | solidity-lean | verdict |
|---|---|---|---|
| `bytes`/`string` key | raw unpadded bytes ++ slot; empty key → `keccak(slot)` | Interpreter.lean:1748-1752 | FAITHFUL |
| `uint`/`bool`/`address`/`enum` key | pad32 right-aligned | right-aligned word | FAITHFUL |
| `int8(-1)` key | sign-extended full word (probe: low-byte-only preimage empty) | `Value.int` full-word two's complement | FAITHFUL |
| nested `m[k1][k2]` | `keccak(h(k2) . keccak(h(k1) . slot))` | `resolveStoragePathSlot` iterates `mappingStorageSlotForKey` (Interpreter.lean:3989-3991) | FAITHFUL (modulo AGG1/AGG2c key forms) |
| `bytesN` key | left-aligned | right-aligned | **AGG1 — WRONG** |
| contract-type key | pad32 address | FNV fallback | **AGG2c — WRONG** |
| struct as mapping value / `arr[i].field` / `s.dynArr[j]` / `s.map[k]` | offsets relative to hashed/derived base slot | `resolveStoragePathSlot` composes `structFieldStorageSlot?` / array-slot / mapping-slot from the hashed base (Interpreter.lean:3985-4030) | FAITHFUL (structure); element packing under AGG3/in-flight |
| bytes/string nested in struct or as mapping value | length-or-short slot at the field/hashed slot, data at `keccak(slot)+i` | same `storeStorageBytesAt`/`loadStorageBytesAt` machinery as top level (placement probe `WithBytes`: bs@1, b@2) | FAITHFUL (placement CONFIRMED; nested value fidelity INFERRED from S5-audited shared code) |

## Checklist of target cases

- [x] Struct field packing: share-slot, doesn't-fit-new-slot, 31+1
  boundary, total span round-up — FAITHFUL (probe + audit)
- [x] Nested struct: whole-slot alignment both sides of the boundary —
  FAITHFUL
- [x] Struct-in-array stride (dyn + fixed), array-in-struct (fixed inline,
  dynamic 1+keccak region), mapping-in-struct placeholder — FAITHFUL
  (placement); element packing of sub-32-byte lanes — AGG3/IN-FLIGHT
- [x] Mapping keys: value vs bytes/string distinction — FAITHFUL;
  bytesN — **AGG1 WRONG**; contract-type — **AGG2c WRONG**; int
  sign-extension, bool, address, enum, uint, nested composition, empty
  bytes key — FAITHFUL
- [x] bytes/string nested in struct / as mapping value — FAITHFUL
- [x] Fixed arrays as fields/vars: `uint8[33]`, `uint8[3]`-in-struct —
  FAITHFUL; non-divisor widths (`uint40[32]`) — AGG3
- [x] Contract-typed members everywhere (state var, struct field, mapping
  key, transient) — **AGG2 WRONG (NEW)**
- [ ] Enum keys carrying an out-of-range deferred-cleanup value used as a
  mapping key (use-site Panic ordering) — UNTESTED, out of scope here
  (constant/cleanup family)

Probe artifacts (scratchpad, not committed): `Layout.sol`, `Layout2.sol`
storage-layout dumps; Forge suite `M.sol`/`M.t.sol` (5 tests; the single
"FAIL" is an intentionally-inverted assertion confirming the low-byte
preimage does NOT hold the int8 value).
