# ABI encode side of complex/nested aggregate types — divergence review

Scope: the head/tail (offset) computation solc's coder-v2 encoder uses for
`abi.encode` / `abi.encodePacked` / return / call-argument encoding of nested
aggregate shapes. This is the ENCODE counterpart to the decode work (D1) and
the single-deref encode work (M4); the nested offset arithmetic below was
previously unmined.

**Result: CLEAN NEGATIVE.** No divergence found. Every shape probed matches
pinned solc 0.8.35 byte-for-byte, and the `encodePacked` type-shape gate
matches solc's `typeSupportedByOldABIEncoder` accept/reject set exactly.
Confidence 90%.

## What was examined

solidity-lean encoder (all in the `SolidCore.Solidity.Source.ABI` namespace):
- `encodeStaticValue?` — `SolidCore/Solidity/ABI.lean:153`
- `encodeDynamicPayload?` — `SolidCore/Solidity/ABI.lean:207` (the recursive
  head/tail for dynamic array / fixed array / tuple)
- `encodeValuesAux?` / `encodeValues?` — `SolidCore/Solidity/ABI.lean:292` /
  `:313` (top-level tuple head origin = `wordBytes * listAbiHeadWords? tys`)
- packed path: `abiEncodePackedValue?` / `abiEncodePackedArrayElement?` /
  `abiEncodePackedArrayValues?` / `abiEncodePackedValues?` —
  `SolidCore/Solidity/Interpreter.lean:5033`–`5116`
- packed type gate: `Ty.isAbiEncodePackedArgShape` /
  `Ty.isAbiEncodePackedArrayElementShape` —
  `SolidCore/Solidity/TypeCheck.lean:4274`–`4332`

solc reference:
- `TypeChecker::typeSupportedByOldABIEncoder` —
  `libsolidity/analysis/TypeChecker.cpp:55`–`69` (the packed accept/reject rule)
- packed argument check — `TypeChecker.cpp:2167`–`2172`

The head/tail origin logic in solidity-lean is uniform and recursive: for every
aggregate, the per-element/per-component offset base is
`wordBytes * (head-word count)` measured from the START of that aggregate's own
head region (`listAbiHeadWords?` for tuples/top-level; `values.length *
elementWords` for dynamic arrays after the length word; `wordBytes * size` for
fixed arrays). This is exactly solc's coder-v2 head/tail split, and it composes
correctly at every nesting depth.

## Byte-for-byte reproductions (interpreter vs `cast abi-encode`, pinned solc)

Each Lean value was encoded via `ABI.encodeValues?` and the hex compared to
`cast abi-encode` (coder v2, the same coder solc always uses for encode).

| Shape | Program | Match |
|---|---|---|
| 1. `S[]`, `S{uint256 a; bytes b}` | `[(7,0xaabb),(9,0x)]` | ✅ identical |
| 2a. `uint256[][]` | `[[1,2],[3]]` | ✅ identical |
| 2b. `uint256[][3]` (fixed-of-dynamic, incl. empty inner) | `[[1],[2,2],[]]` | ✅ identical |
| 3. `(uint256[3], bytes)` (static array + dynamic mixed) | `([11,12,13],0xdead)` | ✅ identical |
| 4. tuple w/ multiple dynamics `(bytes,uint256,bytes)` | `(0xaa,5,0xbbbb)` — first offset `0x60` | ✅ identical |
| 7. empty dynamic values inside aggregates | covered by 1 (`bytes("")`) & 2b (empty `uint256[]`) | ✅ offset points at zero-length tail |

Representative check — shape 1 (`abi.encode((uint256,bytes)[])`), both produce:
```
0x0000..0020  offset to array
   0000..0002  array length
   0000..0040  offset to elem[0]      (rel. to start of offset area)
   0000..00c0  offset to elem[1]
   0000..0007  elem[0].a
   0000..0040  elem[0] inner offset to b (rel. to tuple start = 2 words)
   0000..0002  len(b)=2
   aabb..0000  b
   0000..0009  elem[1].a
   0000..0040  elem[1] inner offset to b
   0000..0000  len(b)=0                 (empty tail, offset still valid)
```
Interpreter output byte-identical. The nested inner-offset origin (`0x40` = the
struct's own 2-word head, not the outer array's) is correct at every level —
this is the classic place offset bugs hide, and it is right here.

## Shape 5 — `abi.encodePacked` over-accept check (CLEAN)

solc rule (`typeSupportedByOldABIEncoder`, TypeChecker.cpp:55-69): reject any
struct; reject any array whose base is a dynamically-sized array (so `bytes` /
`string` as an element are rejected too, since both are dynamically-sized
Array types); allow statically-sized nested arrays.

solidity-lean's `isAbiEncodePackedArrayElementShape` (TypeCheck.lean:4301-4332)
has NO case for `Ty.bytes` / `Ty.string` (they fall to `_ => false`) and
rejects arrays with a dynamic (`none`-sized) inner dimension, while allowing
`some`-sized nested arrays. Structs (`Ty.user` that is neither contract, enum,
nor user-value-type) fall to `false`. This mirrors solc precisely.

Empirically confirmed against pinned solc (`--bin-runtime`), both sides agree:

| Packed arg | solc | solidity-lean gate |
|---|---|---|
| `bytes[]` | REJECTED ("Type not supported in packed mode") | rejected (no `Ty.bytes` element case) |
| `string[]` | REJECTED | rejected (no `Ty.string` element case) |
| `uint256[][]` | REJECTED | rejected (dynamic inner dim → `none`) |
| `uint256[2][3]` | ACCEPTED | accepted (static → recurse) |
| `uint256[2][]` | ACCEPTED | accepted (static base) |

Packed value encoding for the accepted nested-static shapes also matches solc's
rule (array elements padded to 32 bytes, in-place, no length prefix; top-level
narrow scalars packed to their true width via `Tys.packedTopWidths` /
`abiEncodePackedNarrowScalar?`).

## Shape 6 — selector prefix (CLEAN, already covered)

`encodeWithSelector`/`encodeCall` prepend the 4-byte selector and then call the
same `encodeValues?`; ABI offsets are relative to the start of the argument
block (after the selector), so the selector does not shift internal offsets —
matching solc. This is the M-side already recorded in
`docs/solc-encodecall-selector-review.md`; no new nested-offset issue.

## Confidence / caveats

- 90% overall. The head/tail arithmetic was verified both by full manual trace
  of `encodeDynamicPayload?`/`encodeValuesAux?` and by running the real Lean
  encoder and diffing against `cast` for shapes 1–4/7. The packed gate was
  verified against solc source and by compiling against pinned solc.
- Not exhaustively fuzzed: I probed representative instances per shape, not a
  randomized corpus. A deeper nesting (e.g. `S[]` where `S` contains `T[]` of a
  struct with `bytes`) was not individually run, but the encoder is fully
  structurally recursive with the offset origin recomputed per aggregate, so
  there is no plausible depth-specific break; the pieces that would break — the
  per-aggregate head-word origin — are the exact ones verified.
- No Lean semantics were modified (search-only).

## Repro artifacts

Probe file: `scratchpad/EncProbe.lean` (run with
`lake env lean --run`, imports `SolidCore.Solidity.ABI`). Reference bytes via
`cast abi-encode` and `solc-0.8.35 --bin-runtime`.
