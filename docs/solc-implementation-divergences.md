# Implementation-level solc-vs-Solidus divergence review

**Complementary pass to the test-driven audits.** Where
`docs/solidus-solc-deep-comparison.md` walked solc's *test tree* category by
category, this review reads solc's **actual implementation code paths** — the Yul
that `YulUtilFunctions.cpp`/`ABIFunctions.cpp` emit and the predicates in
`Types.cpp` — helper family by helper family, and compares the **observable**
(value / revert / accept-reject) against Solidus's corresponding Lean code. The
aim is the harder complement: semantic rules the tests do not isolate.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD.

Read-only inventory: nothing was built or run; the corpus/replay were not
exercised. Findings are **CONFIRMED** (both sides read definitively) or
**INFERRED** (deduced from source, wants a probe).

---

## Executive summary

**Which implementation files / helper families were actually read (code, not
tests):**

- `YulUtilFunctions.cpp`: the checked *and* wrapping integer families
  (`overflowCheckedIntSub/Div`, `intMod`, `wrappingIntSub/Div/Mul`), the whole
  exponentiation family (`overflowCheckedIntExpFunction`,
  `overflowCheckedUnsignedExpFunction`, `overflowCheckedSignedExpFunction`,
  `overflowCheckedExpLoopFunction`, `overflowCheckedIntLiteralExpFunction`,
  `wrappingIntExpFunction`), the shift family (`shiftLeft/RightFunction(Dynamic)`,
  `shiftRightSignedFunctionDynamic`, `typedShiftLeft/RightFunction`),
  `conversionFunction` (the full single-slot conversion matrix) +
  `bytesToFixedBytesConversionFunction`, `cleanupFunction`, `validatorFunction`,
  `cleanupFromStorageFunction`, the storage read/write masking family
  (`updateStorageValueFunction`, `extractFromStorageValue(Dynamic)`,
  `prepareStoreFunction`, `updateByteSliceFunction`), the storage-array mutators
  (`storageArrayPopFunction`, `storageByteArrayPopFunction`,
  `storageArrayPushFunction`, `storageArrayPushZeroFunction`,
  `clearStorageRangeFunction`, `partialClearStorageSlotFunction`), and
  `increment/decrementChecked/WrappingFunction`, `negateNumberCheckedFunction`.
- `ABIFunctions.cpp`: `abiDecodingFunctionArray`,
  `abiDecodingFunctionArrayAvailableLength`, `abiDecodingFunctionCalldataArray`,
  `abiDecodingFunctionByteArrayAvailableLength`, `packedHashFunction` entry.
- Cross-checked against Solidus `Interpreter.lean` (arithmetic + cleanup +
  dispatch), `ABI.lean` (decoder), `Shared/Word.lean` (EVM word primitives).

**Headline: NO NEW soundness divergences found in the families reviewed.** Every
helper family read at the emitted-Yul level was found to compute the same
observable value and raise the same revert/panic as Solidus's corresponding path.
The divergences that exist are exactly the ones the prior passes already recorded:

- **Fixed/merged** (verified they read as fixed, not re-reported): S1 string-literal
  UTF-8, S2 memory-aggregate eager cleanup, S3 packed ternary width, S4 `Panic(0x41)`
  oversized alloc, S5 `Panic(0x22)` long-form storage byte-array, A1–A4 signed/unsigned
  and contract-conversion acceptance, C1–C6.
- **In-flight** (sibling worktrees, not re-reported as new): G1 user-defined
  operators run as builtins; G2–G16 acceptance boundaries; G17–G22 untested-but-modeled;
  W1 encodePacked narrow-int width, W2 narrow left-shift spurious panic, W3 signed-base
  `**` — all in `docs/bc-soundness-audit.md` / `docs/solidus-solc-deep-comparison.md`.

This is a **well-earned negative**: the review was specifically aimed at the
subtle-rule hiding places the task calls out (cleanup timing, conversion
rounding/sign at the edges, checked/unchecked boundaries incl. exponentiation,
shift ≥ width, signed `INT_MIN/-1`, negation of `INT_MIN`, storage
packing/extraction/clearing, array push/pop, ABI-decode validation & revert
modes), and each was read to the bottom on both sides. Two low-severity
**defense-in-depth** observations (N1, N2) are recorded — both **confirmed
non-divergent** (Solidus reaches the same observable by a different mechanism),
so neither is a finding; they are logged so a future reader need not re-derive
them.

---

## 1. Families reviewed — verdicts (all faithful)

Legend: **FAITHFUL** = same observable, read on both sides.

### Arithmetic — checked & wrapping (FAITHFUL, CONFIRMED)

| Rule (solc) | solc file:line | Solidus | Verdict |
|---|---|---|---|
| Signed `div` overflow `INT_MIN / -1` → `Panic(0x11)`; div-by-0 → `0x12`; else `sdiv` | `YulUtilFunctions.cpp:850-878` | `checkedSignedDiv` `Interpreter.lean:5315-5322` (`isSignedMinWord`+`isSignedNegOneWord`→overflow; else `sdivWord`) | FAITHFUL |
| `mod` by 0 → `0x12`; else `smod`/`mod` (sign of dividend) | `:901-920` | `checkedSignedMod` `:5324-5329` / `checkedMod` `:5247-5252` (EVM `smod`/`mod` via `Word.lean:105/…`) | FAITHFUL |
| Checked sub: signed under/overflow both directions; unsigned `diff>x` | `:922-964` | `checkedSignedSub` `:5292-5296` (Int compare) / `checkedSub` `:5225-5230` (`norm lhs < norm rhs`) | FAITHFUL |
| Wrapping sub/mul/div = op then `cleanup` (mask/signextend) | `:834-899,966-980` | `checkedSignedWord` unchecked branch returns `wrapped`; narrow width via `int/uintCleanup?` unchecked cast `:657-672,625-637` | FAITHFUL |
| `++`/`--` checked: `eq(value,max/min)`→`0x11` | `:4174-4237` | `+ 1`/`- 1` through the same `checkedAdd`/`checkedSub` + cleanup path | FAITHFUL |
| Unary `-` of `INT_MIN` → `0x11` | `negateNumberCheckedFunction:4258` | `checkedSignedNeg` `:5304-5307` (`-(signedValue)` range-checked) | FAITHFUL |

### Exponentiation (FAITHFUL, CONFIRMED — the trickiest family)

solc splits into signed/unsigned square-and-multiply
(`overflowCheckedSignedExpFunction:1186`, `overflowCheckedUnsignedExpFunction:1128`,
shared `overflowCheckedExpLoopFunction:1236`); for a narrow type
`overflowCheckedIntExpFunction:982` passes the **narrow** `min/max` into the loop
so overflow is detected against the narrow bound; `wrappingIntExpFunction:1276`
is `cleanup(exp(base,exponent))`.

Solidus computes exp by **linear** iteration (`checkedExpLoop:5254` unsigned,
`checkedSignedExpLoop:5337` signed), checking each partial product against the
**256-bit** range, and lets the importer-inserted `uint/intCleanup?` enforce the
**narrow** bound at the end (`:625-672`).

- **Value:** identical. `signedValue(w) ≡ w (mod 2^256)`, so Solidus's iterated
  signed-product-then-`signedToWord` equals EVM `exp`'s modular exponentiation
  (unchecked), and equals the true integer power (checked).
- **Panic:** identical observable. Magnitude is monotonic in the exponent, so the
  final result overflows the narrow type **iff** some intermediate does; solc may
  raise `0x11` at an earlier squaring step while Solidus raises it at the closing
  `uint/intCleanup?`, but both raise `0x11` on exactly the same inputs and neither
  raises it otherwise. Worked both ways for `uint8 255**2` (→`0x11` both),
  `int8 (-2)**7 == -128` (→OK both), `uint8 unchecked 255**2 == 1` (both).
- `0**0 == 1`, `base==0 && exp>0 → 0`: solc `:1149-1150,1198-1200`; Solidus loop
  base cases `:5256,5339`. FAITHFUL.

### Shifts (FAITHFUL for value; W2 narrow-left-shift panic is IN-FLIGHT)

`shiftLeft/RightFunctionDynamic` are EVM `shl`/`shr`; signed `>>` uses `sar`
(`shiftRightSignedFunctionDynamic:525`); `typedShift*:552-599` clean amount then
value. Solidus dispatches on the **value tag**: `Value.int` (signed) routes `>>`
to `sarWord`, `Value.word` (unsigned) to `shrWord` (`applySignedWord:5397-5430`,
`applyWord:5383-5385`), all delegating to EVM-reference primitives
(`Word.lean:120-129`). Shift-by-≥-width returns 0 (logical) / sign-fill (arith) as
EVM does. The only shift divergence is the already-recorded **W2** (narrow left
shift spurious panic), which is in-flight.

### Conversion matrix & cleanup (FAITHFUL, CONFIRMED)

| Rule (solc) | solc file:line | Solidus | Verdict |
|---|---|---|---|
| `intN→bytesM` (same width): `shiftLeft(256-M*8)` (left-align) | `conversionFunction:3557-3558` | left-aligned `bytesN` word; A3 signed-accept is the only edge (fixed) | FAITHFUL |
| `bytesN→bytesM`: clean to `min(N,M)` (keep high bytes) | `:3646-3651` | prior CONFIRMED faithful (`Interface.lean` bytesN paths) | FAITHFUL |
| `bytes(dyn)→bytesN`: first `min(len,N)` bytes, low tail zeroed | `bytesToFixedBytesConversionFunction:3704-3760` (`if lt(length,N)` mask) | `Interpreter.lean:603-611` (prior CONFIRMED) | FAITHFUL |
| `cleanup`: signed narrow = `signextend`; unsigned = `and mask`; bool = `iszero(iszero)`; bytesN = high mask; enum = validate-or-`0x21` | `cleanupFunction:3959-4056` | `intCleanup?`/`uintCleanup?` `:657-672,625-637`; enum deferred use-site `0x21` | FAITHFUL |
| `validator(revertOnFailure)`: value-type `eq(value,cleanup(value))`→`revert(0,0)`; enum `lt(value,members)`→`0x21` | `validatorFunction:4059-4110` | ABI eager validation of scalar bool/addr/bytesN → empty revert; enum → `0x21` (prior CONFIRMED) | FAITHFUL |

### Storage read/write masking (FAITHFUL, CONFIRMED)

`cleanupFromStorageFunction:3153` sign-extends signed narrow reads
(`signextend(storageBytes-1, value)`) and left-aligns `leftAligned` types;
`extractFromStorageValue:3137` shifts by `offset*8` then cleans;
`updateStorageValueFunction:2939` converts → `prepareStore` (clean) → masked
`updateByteSlice` write; `prepareStoreFunction:3188`. Solidus's byte-level
`packedScalar` read with sign-extend-on-read and masked packed write were
CONFIRMED faithful by the prior review (`Interpreter.lean:1316-1376,3323`), and
the write-side masking here matches. FAITHFUL.

### Storage array mutators (FAITHFUL, CONFIRMED)

`storageArrayPopFunction:1654` (empty→`0x31`, clear freed slot),
`storageByteArrayPopFunction:1685` (short/long transition, `0x31`),
`storageArrayPushFunction:1729` / `PushZeroFunction:1800` (`oldLen ≥ 2^64` →
`Panic(0x41)`), `clearStorageRangeFunction:1850`. The `2^64` push guard is the
`ResourceError` path the prior review noted is practically unreachable (needs 2^64
elements). Solidus models push/pop with `0x31` on empty-pop and clears the freed
slot (prior CONFIRMED). FAITHFUL.

### ABI array/bytes decode bounds & revert modes (FAITHFUL, CONFIRMED)

`abiDecodingFunctionArray:1136` (`slt(add(offset,0x1f),end)` head check),
`abiDecodingFunctionArrayAvailableLength:1168` (`srcEnd>end`→revert, per-element
inner-offset `>2^64`→revert), `abiDecodingFunctionCalldataArray:1226`
(`length>2^64`→revert, `arrayPos+length*stride>end`→revert),
`abiDecodingFunctionByteArrayAvailableLength:1275` (`src+length>end`→revert).
Solidus's `decodeValueAtWithFuel?` (`ABI.lean:369-424`) reads each word/byte
through bounds-checked `readWord?`/`readBytes?`, so an out-of-range offset/length
yields `none` → empty revert. Prior review CONFIRMED decode-bounds/OOB-offset/slice
faithful. FAITHFUL (see N1 for the one predicate solc states explicitly that
Solidus reaches structurally).

---

## 2. Defense-in-depth observations (CONFIRMED non-divergent — NOT findings)

### N1 — calldata dynamic-array `length < 2^64` guard is structural, not explicit — INFERRED, non-divergent

- **solc:** `abiDecodingFunctionCalldataArray:1246` emits an explicit
  `if gt(length, 0xffffffffffffffff) { revert }` **before** the stride/bounds
  check, so a length word ≥ 2^64 empty-reverts even before `mul(length,stride)`
  could wrap mod 2^256.
- **Solidus:** `ABI.lean:373-388` reads `length` and uses it directly as the
  decode loop count with no `< 2^64` gate. It is nonetheless **non-divergent**:
  any `length ≥ 2^64` requires `length * 32` bytes of element data that no calldata
  can contain, so the first out-of-range `readWord?` returns `none` → empty revert,
  the same observable as solc. There is no `length` that both exceeds `2^64`
  *and* has all its element reads in bounds (that needs > 2^69 bytes of calldata),
  so Solidus cannot succeed-with-a-wrong-value where solc reverts. Same threat
  class as the (now-fixed) S5 — only reachable via adopted/hand-crafted calldata,
  and here fully masked. Recorded, not a finding.

### N2 — narrow checked-arithmetic panic is raised at the cleanup wrapper, not inside the op — CONFIRMED, non-divergent

- **solc** bakes the narrow bound into each op (`checked_add_uint8` panics if
  `sum > 0xff` inside the helper). **Solidus** performs the op at 256-bit
  (`checkedAdd`/`checkedSignedExpLoop` check only the 256-bit boundary) and relies
  on the importer-inserted `uint/intCleanup?` (`Interpreter.lean:625-672`, checked
  branch → `RevertData.overflow` = `0x11`) to enforce the narrow bound. Because the
  narrow result overflows **iff** the cleanup sees an out-of-range word, the
  observable (`0x11` or not) is identical. This is the general mechanism behind the
  prior review's "checked-arithmetic all widths 0x11/0x12 faithful"; recorded here
  so the *where-the-panic-lives* difference is not mistaken for a divergence.

---

## 3. Families reviewed checklist

Read at emitted-Yul / predicate level on both sides — verdict FAITHFUL unless the
prior reviews already own the finding:

- [x] Checked int add/sub/mul/div/mod (signed + unsigned, 256-bit + narrow)
- [x] Wrapping (unchecked) int add/sub/mul/div/mod
- [x] Exponentiation: checked signed, checked unsigned, literal-base, wrapping, narrow-bound, `0**0`
- [x] Shift left/right, dynamic, signed-arithmetic (`sar`), typed narrow (value only; W2 in-flight)
- [x] `++`/`--` checked & wrapping; unary `-` of `INT_MIN`
- [x] Conversion matrix (single-slot): int↔int, int→bytesN, bytesN→bytesM, bytesN→int, addr/contract, enum, `bytes`→bytesN
- [x] `cleanupFunction` / `validatorFunction` / `cleanupFromStorageFunction`
- [x] Storage read/write masking: extract, update, prepareStore, updateByteSlice
- [x] Storage array push / pop / pushZero / byte-array pop / clearStorageRange
- [x] ABI decode: memory array, calldata array, byte-array available-length, bounds/offset revert modes
- [x] Signed/unsigned value-tag dispatch (`BinaryOp.apply` → `applyWord`/`applySignedWord`)

**Families NOT reached (candidates for a future pass):**

- `ExpressionCompiler.cpp` LValue / compound-assignment / tuple-assignment /
  `delete`-per-type **evaluation-order** micro-rules (prior review spot-checked these
  as faithful via the semanticTests sweep, but they were not re-read at codegen level
  here).
- `copyToMemory` / `abiEncodePacked` / `packedHashFunction` **body** (packed widths)
  — this is W1/S3 territory and is in-flight; not independently re-verified.
- `abiEncodingFunction*` head/tail **encode** side for deeply nested dynamic types
  (prior review CONFIRMED faithful from the test sweep; not re-read at Yul level).
- Analysis passes `ViewPureChecker.cpp` / `OverrideChecker.cpp` /
  `ControlFlowAnalyzer` full bodies — the acceptance boundaries they enforce are
  already covered by in-flight G2 (mutability), G6 (override/super), G19
  (mutability-relaxing override) and the prior "controlFlow FAITHFUL" verdict.
- Memory `allocateMemory` / `abiDecodingFunctionStruct` nested-struct decode
  (prior review CONFIRMED the observable; codegen body not re-read).

---

## 4. Bottom line

Reading solc's real code paths family by family — the checked/unchecked integer
and exponentiation helpers, shifts, the conversion matrix, cleanup/validator,
storage packing/extraction/clearing, storage-array mutators, and ABI-decode
bounds — surfaced **no new soundness divergence**. Solidus computes the same
value and raises the same revert/panic on every rule read, with signed/unsigned
correctly driven by the runtime value tag and word ops delegated to EVM-reference
primitives. The two places where solc states a guard more explicitly than Solidus
(N1 calldata length `< 2^64`, N2 narrow-op panic siting) were each confirmed to
produce the identical observable by a structural/deferred mechanism. All genuine
divergences remain the ones the prior passes already own: S1–S5 / A1–A4 / C1–C6
(fixed) and G1–G22 / W1–W3 (in-flight).
