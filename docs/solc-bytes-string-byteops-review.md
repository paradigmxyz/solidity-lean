# Byte-level operations on `bytes` / `string` / `bytesN` vs solc 0.8.35

**Scope:** element access, length, mutation, comparison, concat, slicing, `new bytes`,
`bytesN` conversions, and the associated accept/reject rules.
**Ground truth:** pinned solc 0.8.35 (`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`)
+ Forge 1.5.1 (legacy codegen: optimizer=false, no via_ir).
**Semantics under test:** solidity-lean at `/Users/dan/Projects/solidity-lean`.
**Method:** minimal programs run against real solc (accept/reject) and Forge (byte-exact
values), cross-read against `TypeCheck.lean` / `Interpreter.lean` / `Interface.lean`.

## Verdict: CLEAN NEGATIVE (confidence ~92%)

Every one of the 8 mission areas matches solc byte-for-byte / accept-reject. No divergence
found. The central risk — solidity-lean stores `bytesN` **right-aligned** (meaningful bytes
in the low positions) while solc stores it **left-aligned** — is reconciled consistently and
correctly at every read site. Details below; each area lists the exact program, solc result,
solidity-lean result, and the governing `file:line`.

---

## Key representation fact

`bytesN` = `Value.word` holding the value **right-aligned**; solc holds it left-aligned.
Every content read goes through `wordToBytesBE size` (`Interpreter.lean:38-41`), which
extracts the **low `size` bytes big-endian** (index 0 = most-significant = leftmost content
byte). Writes go through `bytesPrefixRightPadded` / `bytesToWordBE` (`:26-45`). Because reads
and writes are symmetric through these helpers, the right-aligned model reproduces solc's
left-aligned observable semantics. The only leak hazard (`<<`, `~` push bits above the lane)
is masked by an inserted `fixedBytesCast size size` cleanup at the frontend
(`Interface.lean:6797-6849`), matching solc `cleanup_t_bytesN`.

---

## 1. Fixed `bytesN` indexing — byte order, read-only, OOB

Program / solc (Forge `testIdx`, `testUintToBytesIdx`):
```solidity
bytes4 b = 0x12345678;   b[0] == 0x12,  b[3] == 0x78     // index 0 = high/left byte
bytes2(uint16(0x1234));  [0]==0x12, [1]==0x34
```
- **solc:** index 0 = most-significant byte; PASS.
- **solidity-lean:** `fixedBytesIndex?` = `listGet? (wordToBytesBE size value) (norm index)`
  (`Interpreter.lean:602-609`) — big-endian, index 0 = leftmost. **Match.**
- **Read-only:** result typed `bytesN 1` with `lvalue := false` (`TypeCheck.lean:5717-5727`);
  assignment site requires `lhs.lvalue` (`TypeCheck.lean:7318`). solc rejects `b[0]=0xff`
  (`bytesNIdxAssign` REJECT). **Match (over-accept negative).**
- **Constant OOB** rejected at compile time (`i < size`, `TypeCheck.lean:5722`) = solc
  TypeError 1859. **Runtime OOB** → `RevertData.indexOutOfBounds` = Panic 0x32
  (`Interpreter.lean:607`, `:296`). **Match.**

## 2. Dynamic `bytes` indexing + element assignment

- Read `b[i]` → `bytes1`, lvalue inherited (`TypeCheck.lean:5710-5716`); interpreter
  `Value.index?` (`Interpreter.lean:566-572`), OOB Panic 0x32.
- Write `b[i]=x` allowed for memory/storage bytes; `Value.setIndex?` writes `normByte w`
  (low byte) at index (`Interpreter.lean:744-751`), OOB Panic 0x32, non-word RHS typeMismatch.
- **Match** (value + accept/reject).

## 3. `string` has NO index or length — both REJECTED

| program | solc | solidity-lean |
|---|---|---|
| `s[0]` on `string memory` | REJECT | REJECT — `Expr.index` catch-all `other => error` (`TypeCheck.lean:5753`) |
| `s.length` on `string` | REJECT ("Member length not found") | REJECT — `hasLengthMember` false for string (`TypeCheck.lean:4209-4214`, gate `:5663`) |

`bytes(s).length` works on both (string→bytes conversion first). **Match (over-accept negatives).**

## 4. Comparison

| program | solc | solidity-lean |
|---|---|---|
| `bytes4 == bytes4` | ACCEPT | ACCEPT — `isEqualityComparable` includes bytesN (`TypeCheck.lean:3469`) |
| `bytes4 < / > bytes4` | ACCEPT (big-endian unsigned) | ACCEPT — `isRelationalOperand` includes fixedBytes; `ltWord` unsigned (`TypeCheck.lean:400-414`, `Interpreter.lean:5600`) |
| `string == string` | REJECT | REJECT — `"equality on non-value type"` (`TypeCheck.lean:7205`) |
| `bytes == bytes` | REJECT | REJECT — same gate |

Forge `testLt`: `bytes4(0x00000001) < bytes4(0x00000002)` and `bytes4(0x01000000) >
bytes4(0x00ffffff)` both hold. Right-aligned numeric compare = big-endian lexicographic for
same-size bytesN (only same size is ever comparable). **Match.**

## 5. `bytes.concat` / `string.concat`

Forge `testConcat`: `bytes.concat(bytes4 0xaabbccdd, bytes2 0xeeff, bytes("XY"))` →
`hex"aabbccddeeff5859"`, length 8 (no inter-arg padding; bytesN contributes N bytes).
- **solidity-lean** lowers both to packed encoding (`Interface.lean:4543-4574`);
  `abiEncodePackedValue?` emits `wordToBytesBE size` for bytesN and raw bytes for `bytes`
  (`Interpreter.lean:5064-5073`); empty concat → `[]` (`:5127`). **Byte-exact match.**
- Arg rules: `bytes.concat` accepts bytes/bytesN/string-literal, rejects string-typed value
  (`checkBytesConcatArgs`, `TypeCheck.lean:4415-4423`); solc `bytesConcatStr` REJECT,
  `strConcatBytes` REJECT, `stringConcat`/`bytesConcatN` ACCEPT — all match.

## 6. Calldata slice `b[start:end]`

Forge `testSliceCd`: `this.g(hex"00010203040506")` with `return b[2:5]` → `hex"020304"`.
- **Bounds / revert kind:** solc — `end>length`, `start>end`, `start` OOB all → **plain
  empty revert** (staticcall returndata length 0, no Panic selector), verified in `S.t.sol`.
  solidity-lean `sliceListByWords?` returns `RevertData.empty` on `!(start<=stop &&
  stop<=length)` (`Interpreter.lean:704-713`) — plain `revert(0,0)`, explicitly distinct from
  index Panic 0x32. **Match.**
- **Defaults:** `b[:e]`→start 0, `b[s:]`→stop length (`Interpreter.lean:696-703`).
- **Memory slice REJECTED:** solc `memSlice` / `arrMemSlice` REJECT ("only dynamic calldata
  arrays"); solidity-lean requires `dataLocation? == calldata` (`TypeCheck.lean:5767`).
  **Match (over-accept negative).**
- Note: `string calldata` slicing IS accepted by solc (`strSlice` ACCEPT) and by
  solidity-lean (`TypeCheck.lean:5760`) — consistent, not a divergence.

## 7. `new bytes(n)` and `bytesN` conversions

- `new bytes(3)` → zero-filled length 3 (Forge `testNewBytes`); solidity-lean
  `List.replicate size 0` (`Interpreter.lean:6667-6673`). **Match.**
- `bytes4(bytes32)` keeps HIGH 4 bytes: Forge `testCast`/`testBytes4Bytes32Trunc` —
  `bytes4(0x1122...) == 0x11223344`, `bytes4(bytes32(uint256(1))) == 0`. solidity-lean
  `fixedBytesCast?` = `bytesPrefixRightPadded targetSize (wordToBytesBE sourceSize)` — keeps
  leftmost bytes, right-pads (`Interpreter.lean:611-621`). **Match.**
- `bytes32(uint256(0xabcd))` left-aligned: Forge `testBytes32Uint` — byte[30]=0xab,
  byte[31]=0xcd, byte[0]=0. Identity on right-aligned word. **Match.**
- `bytesN.length` compile-time constant (Forge `testBytesNLen`: `bytes4(0).length==4`) —
  `hasLengthMember` true for bytesN (`TypeCheck.lean:4211`). **Match.**

## 8. `abi.encodePacked` of bytes/string/bytesN

Forge `testEncodePacked`: `abi.encodePacked(bytes4 0xdeadbeef, "hi", bytes1 0x42,
uint16 0x0102)` → `hex"deadbeef6869420102"` (no padding). Same packed path as §5.
**Byte-exact match.**

---

## Confidence & residual risk

- Overall **~92%**. All observable behaviors reproduced against real solc/Forge; the Lean
  paths were read to root definitions.
- The −8% is the usual coverage caveat: `bytes storage` element assignment to *packed slots*
  and storage `bytesN`-key mapping paths were reasoned about (comments at
  `Interpreter.lean:1788-1793`, `:488-490`, `:1489-1490`) but not each exercised with a fresh
  storage-round-trip Forge case in this pass; the short-string (<32) vs long-string storage
  layout boundary is adjacent D-MEM territory and out of this review's element-op scope.
- No new lanes or fixtures were added; this is a read/reproduce audit only.

## Files touched (read-only)

`SolidCore/Solidity/TypeCheck.lean` (index 5702-5754, member/length 5663-5665 + 4209-4214,
slice 5755-5789, comparison 3453-3477 + 7180-7210, concat 4415-4430),
`SolidCore/Solidity/Interpreter.lean` (fixedBytesIndex? 602-609, fixedBytesCast? 611-631,
slice 694-731, setIndex? 733-771, applyWord 5584-5610, packed 5053-5081, new bytes 6667-6673),
`SolidCore/Solidity/Interface.lean` (concat/cast lowering 4543-4574 + 6718-6731, bitop cleanup
6797-6849, isBytesConcatArg 3797-3814).
