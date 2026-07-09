# Implementation-level solc-vs-solidity-lean divergence review (round 12 — ABI encoder deep edges + event/error encoding corners)

**Round 12 of the campaign** (the tenth `divergences-*` doc), the plan's P2
mop-up. This round adversarially samples the ABI encoder at the depths the earlier
codec rounds (div-1,-2,-5, WELL-MINED-CLEAN at shallow depth) under-sampled:
function-type element inside a tuple, tuples-in-tuples, deeply nested
`T[][]` / `string[]` round-trips, `abi.encodeCall` / `abi.encodeWithSignature`
dynamic-arg edges, and the event/error encoding deep corners (indexed
reference-type topic hashing, anonymous-event topic layout).

solc ground truth is the pinned `solc 0.8.35` via Forge (byte-exact `abi.encode`
output + recorded log topics); solidity-lean is read to the rule in
`SolidCore/Solidity/Interpreter.lean` + `Interface.lean` and hand-simulated against
each Forge byte string. solc source (v0.8.35, `/Users/dan/Projects/solidity-src`,
commit `47b9dedd`) READ-ONLY. Nothing was built/run for solidity-lean. Findings are
**CONFIRMED** (solidity-lean algorithm read + Forge byte-exact cross-check).

---

## Executive summary

**This is an EARNED-NEGATIVE round: zero new divergences.** Every ABI-encoder deep
edge and event/error corner sampled reproduces solc's bytes/topics exactly.

**Surfaces read this round (both sides):**

- **Nested dynamic ABI encode** — `abiEncodeDynamicPayload?` head/tail with the
  offset base `wordBytes * len * elementWords` (`Interpreter.lean:4613-4694`),
  `abiEncodeValuesAux?` top-level head/tail (`:4698-4720`) ↔ solc
  `ABIFunctions::tupleEncoder`. Forge cross-check: `uint256[][]`, `string[]`.
- **Function-type element** — `abiStaticBytes? Ty.externalFunction` = `addr(20)‖
  selector(4)‖8·0x00` (`Interpreter.lean` `abiStaticBytes?`), decode with strict
  zero-padding check (`:4778-4790`) ↔ solc's 24-byte left-aligned function encoding.
- **Tuple-in-tuple / struct-with-dynamic** — `abiEncodeStaticTupleValues?` /
  dynamic `encodeTupleValues` (`:4600-4607`, `:4661-4694`).
- **`encodeCall` / `encodeWithSignature`** — `Expr.abiEncodeWithSelector`
  (`Interpreter.lean:6347-6361`), selector ‖ tuple-encoded args.
- **Event topics** — `abiEventTopic?` / `abiEventIndexedBytes?` (`:4870-4915`),
  reference-indexed → `keccak(per-element word-padded, NO length)`; anonymous →
  `EventDecl.toCore.topic? := none` (`Interface.lean:18632-18637`,
  `selectorEntry?` `:7651-7652`).

| # | Target | Verdict | Forge cross-check |
|---|--------|---------|-------------------|
| N1 | nested `uint256[][]` head/tail + offset base | faithful | byte-exact |
| N2 | `string[]` (dynamic-of-dynamic) | faithful | byte-exact |
| N3 | function-type element in tuple (`(uint, fn)`) | faithful | byte-exact |
| N4 | tuple-in-tuple / struct-with-`bytes` | faithful | byte-exact |
| N5 | `abi.encodeCall` (empty args) | faithful | byte-exact |
| N6 | `abi.encodeWithSignature` dynamic arg | faithful | byte-exact |
| N7 | indexed dynamic-array topic hashing | faithful | topic-exact |
| N8 | anonymous-event topic layout (no signature topic0) | faithful | topic-count + values |

**NEW divergences this round: 0. Earned negative.** This closes backlog items 9,
10, and 13 (the abstraction-vs-concrete ABI/event surfaces) with both sides read
to the rule + Forge byte-exact confirmation.

---

## Earned negatives (both sides read + Forge byte-exact)

### N1 — nested `uint256[][]` head/tail + offset base

`abi.encode([[1],[2,3]])` (Forge, solc 0.8.35):

```
20                       outer offset (abi.encode wraps the single dynamic arg)
02                       outer length
40  80                   elem offsets (relative to start after length)
01  01                   elem[0]: len 1, [1]
02  02  03               elem[1]: len 2, [2,3]
```

solidity-lean `abiEncodeValues? [dynamicArray (dynamicArray uint256)]`: top-level dynamic
arg ⇒ head `0x20`, tail = `abiEncodeDynamicPayload?`. Inner: `abiHeadWords?
(dynamicArray uint256) = 1` ⇒ `initialOffset = 32·2·1 = 0x40`; `encodeValues`
threads offsets `0x40, 0x40+|elem0|=0x80`, emits `length ‖ heads ‖ tails`. The
offset base is measured from the start of the head region (right after the length
word) — exactly solc's convention. Reproduces the bytes verbatim. Round-trip
`abi.decode` back to `[[1],[2,3]]` confirmed (Forge `assertEq`).

### N2 — `string[]` (dynamic array of dynamic elements)

`abi.encode(["hi","world!!"])` reproduces byte-for-byte: outer offset `0x20`,
length `2`, element offsets `0x40`/`0x80`, then each string as `len ‖
right-padded-bytes` (`0x02 ‖ "hi"·pad`, `0x07 ‖ "world!!"·pad`). solidity-lean's
`abiEncodeDynamicPayload? Ty.bytesCalldata` = `len ‖ abiPadRightWord bytes`
(`:4614-4615`) inside the same head/tail machinery.

### N3 — function-type element in a tuple

`abi.encode(uint256(7), fn)` (Forge): `…0007` ‖ `7fa9385b…4fb95e8c` (24 bytes:
20-byte address ‖ 4-byte selector) ‖ `00000000_00000000` (8-byte right pad). Both
elements are static, so head-only. solidity-lean `abiStaticBytes? Ty.externalFunction`
emits `wordToBytesBE 20 addr ‖ wordToBytesBE 4 selector ‖ replicate 8 0` — the
identical 24-byte-left-aligned word. Decode strictly checks the 8-byte tail is
zero (`:4785`).

### N4 — tuple-in-tuple / struct with a dynamic field

`abi.encode(uint8(5), Inner{a:9, b:hex"aabb"})` (Forge): `05` (head) ‖ `0x40`
(offset to the dynamic `Inner`) ‖ Inner tail `09 ‖ 0x40 ‖ 0x02 ‖ aabb·pad`.
solidity-lean nests `encodeTupleValues` with head-words `= listAbiHeadWords?` and the
per-tuple offset base `wordBytes · headWords` (`:4686-4690`) — same layout.

### N5/N6 — `encodeCall` / `encodeWithSignature`

- `abi.encodeCall(f, ())` = the bare 4-byte selector `0x3b1f03cd`; solidity-lean
  `abiEncodeWithSelector selector [] []` = `selector ‖ []`. Match.
- `abi.encodeWithSignature("f(uint256[])", new uint256[](0))` =
  `0x7bc5bbbf ‖ 0x20 ‖ 0x00` (selector ‖ offset ‖ empty-array length). solidity-lean
  encodes the dynamic arg with head `0x20` + tail `length 0`. Match.

### N7 — indexed dynamic-array topic hashing (deep corner)

For `event Arr(uint256[] indexed a)` with `a=[1,2]`, Forge's recorded `topics[1]`
equals `keccak256(abi.encodePacked(uint256(1), uint256(2)))` — i.e. the per-element
**word-padded** encoding **without** the length word (ruled out `keccak(abi.encode)`
and `keccak(length‖elems)`, both of which Forge shows differ). solidity-lean
`abiEventTopic?` for a hashed-indexed reference type computes
`keccak(abiEventIndexedBytes? false ty value)`, and `abiEventIndexedArrayBytes?`
pads each element to a word (`padDynamic := true`) with **no length prefix**
(`:4888-4894`) — exactly `keccak(packed word-padded elements)`. Match. (A top-level
indexed `bytes`/`string` uses `padDynamic := false` ⇒ `keccak(raw bytes)`, also
matching solc.)

### N8 — anonymous-event topic layout

For `event AnonTwo(uint256 indexed x, uint256 indexed y) anonymous`, Forge shows
the log carries **2** topics (`topics[0]=x`, `topics[1]=y`) with **no** signature
topic0. solidity-lean omits the signature topic for anonymous events: `EventDecl.toCore`
sets `topic? := none` when `decl.anonymous` (`Interface.lean:18632-18637`) and
`selectorEntry?` returns `none` (`:7651-7652`), so the emitted topics are exactly
the indexed values. Match (and anonymous permits up to 4 indexed, non-anonymous 3
— a consequence of dropping the signature topic, which this layout respects).

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round (both sides + Forge byte/topic-exact):**

- [x] nested `T[][]` head/tail + offset base — **FAITHFUL** (N1)
- [x] `string[]` dynamic-of-dynamic — **FAITHFUL** (N2)
- [x] function-type element in tuple — **FAITHFUL** (N3)
- [x] tuple-in-tuple / struct-with-dynamic — **FAITHFUL** (N4)
- [x] `abi.encodeCall` — **FAITHFUL** (N5)
- [x] `abi.encodeWithSignature` dynamic arg — **FAITHFUL** (N6)
- [x] indexed dynamic-array topic hashing — **FAITHFUL** (N7)
- [x] anonymous-event topic layout — **FAITHFUL** (N8)

**Still NOT reached (acceptance-only / lower-priority residue):**

- `abi.encodeCall` full argument-tuple TYPE-MATCH acceptance (arity + implicit
  conversion against the function-pointer's declared params) — an acceptance rule,
  importer-masked on a solc-validated corpus; the selector + arg-encoding *values*
  are faithful (N5).
- `blockhash`/`blobhash` out-of-window acceptance (values are laned; the window
  bound is a responder-answered / acceptance edge).
- **Round-10 (DL1-gated)** transient-storage slot ORDER; **Memory-round-3
  (M1-gated)** memory-ref alias family — both await their fix landing on `main`.

---

## Bottom line

Round 12 adversarially sampled the ABI encoder at depth and the event/error
encoding corners — the last abstraction-vs-concrete surfaces in the backlog (items
9, 10, 13) — and found **nothing new**: nested `T[][]`/`string[]`, function-type
elements, tuple-in-tuple, `encodeCall`/`encodeWithSignature`, indexed dynamic-array
topic hashing (`keccak` of packed word-padded elements, no length), and
anonymous-event topic layout (no signature topic0) all reproduce solc's exact bytes
and topics, confirmed by Forge against the pinned solc. This is an **earned
negative**, consistent with the codec having been WELL-MINED-CLEAN across five
prior rounds; the re-derived ABI/event layout matches solc to the byte even at the
deepest nestings.

**NEW divergences this round: 0 (earned negative).** The remaining productive work
is the two fix-gated rounds (Round-10 post-DL1, Memory-round-3 post-M1); the
acceptance-only residue (encodeCall type-match, blockhash/blobhash window) is
importer-masked and low-priority.
</content>
