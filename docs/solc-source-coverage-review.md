# Deep solc-source coverage review — additional gap inventory

**Method.** A source-level read of solc **v0.8.35** (`/Users/dan/Projects/solidity-src`,
tag `v0.8.35`, commit `47b9dedd` — the exact source of this project's pinned
binary) compared against this repo's executable semantics
(`SolidCore/Solidity/{Interface,Interpreter,TypeCheck,Checked,ABI}.lean`,
importer `scripts/solc_ast_to_lean_source.py`), at **finer-than-node-kind
granularity** — the individual conversion, cleanup, member, ABI, and panic
*rules*. The prior audits (`docs/solidity-feature-coverage.md`,
`docs/bc-soundness-audit.md`) established that node-kind coverage is near-total
and that the frontier is sub-node; this review works that frontier.

solc source actually read (primary sources of truth):
- `libsolidity/ast/Types.cpp` / `Types.h` — `isImplicitlyConvertibleTo`,
  `isExplicitlyConvertibleTo`, `commonType`, `mobileType`, `fitsIntegerType`,
  `MagicType::members`, `*Type::nativeMembers`, `TypeType::members`.
- `libsolidity/codegen/YulUtilFunctions.cpp` — `cleanupFunction`,
  `validatorFunction`, `cleanupFromStorageFunction`, `extract_byte_array_length`,
  panic sites.
- `libsolidity/codegen/ABIFunctions.cpp` — head/tail encode, `abiEncodePacked`,
  `abiDecodingFunction*` (per-element validation, bounds).
- `libsolidity/codegen/ExpressionCompiler.cpp` — `new T[]` allocation panic.
- `libsolidity/analysis/TypeChecker.cpp` — `visit(Conditional)`, call options,
  try/catch, delete.
- `liblangutil/Scanner.cpp` — string-literal escape decoding.
- `libsolutil/ErrorCodes.h` — the Panic catalogue.

This is a **review/inventory only** — nothing was built or run; the corpus and
importer were not exercised. Findings marked **CONFIRMED** were read on both
sides definitively; **INFERRED** were deduced from solc + repo source and want a
probe to nail down the exact observable.

---

## Executive summary

The node-kind audit's conclusion still holds — there is no wholly un-modeled
construct — but reading solc's type system and codegen line-by-line surfaced
**14 new sub-node gaps** the prior audits did not see, including **5 new
value-soundness (wrong-observable) risks** and **4 new acceptance-soundness
(over-accept) risks**. None overlaps the already-recorded W1/W2/W3 wrong-value
findings.

**The single most important new finding is a wrong-value bug in regular string
literals:** `Literal.string` is lowered to Unicode **codepoints**, not the
**UTF-8** bytes solc stores (`Interface.lean:3476-3478`, and the `bytesN` path at
`:2988-2989`). Any regular `"..."` literal containing a non-ASCII character
(reachable via `\uXXXX` escapes, which solc allows inside ordinary strings)
produces the wrong bytes, the wrong `bytes(s).length`, and — most dangerously —
the wrong `keccak256`/`abi.encodePacked` hash. The `unicode"..."` and hex-string
paths are correct (they use `stringUtf8Bytes`); only the plain-string path is
wrong, which is exactly why the "unicode/hex-string literals SUPPORTED" prior
row did not catch it.

**Ranked NEW soundness-risk findings (wrong observable value):**

1. **S1 — regular string literal → codepoints, not UTF-8** (CONFIRMED, HIGH).
   `"é"` → `[0xE9]` in-repo vs `[0xC3,0xA9]` in solc; corrupts bytes,
   `.length`, and every `keccak256(bytes(lit))`/`encodePacked`.
   `Interface.lean:3476-3478`, `:2988-2989`.
2. **S2 — calldata narrow-int/enum *array/tuple/struct-element* cleanup is
   deferred (lazy), where solc validates eagerly at decode** (CONFIRMED). A
   dirty `uint8[]`/enum element that is never used lets a program *succeed* (or
   revert late) where solc reverts empty at entry. `ABI.lean:446-452` lazy
   decoder used at `:684,928`; strict decoder `:454-460` exists but is unused.
3. **S3 — ternary inside `abi.encodePacked` packs using the then-branch width,
   not the ternary's common type** (CONFIRMED). `encodePacked(c ? aUint8 :
   bUint256)` packs 1 byte instead of 32 → wrong hash. `Interface.lean:4818` vs
   the correct common type at `TypeCheck.lean:6882-6887`.
4. **S4 — `Panic(0x41)` oversized-array allocation is effectively dead on the
   production path** (INFERRED; partly contradicts B7's "0x41 exact PARITY").
   `new bytes(2**256-1)` returns a giant list and never panics, because
   `memoryAllocationLimit?` defaults to `none` in every production `Context`
   (`Interpreter.lean:1662-1671, 1659`; limit set only in witnesses); solc's
   threshold is a fixed `0xffffffffffffffff` (`ExpressionCompiler.cpp:1261-1268`).
5. **S5 — `Panic(0x22)` for a long-form storage byte-array with decoded length
   `< 32` is not raised** (INFERRED). solc panics
   (`YulUtilFunctions.cpp:1360-1379`); the repo models only the short-form check
   and silently accepts the long/odd branch (`Interpreter.lean:2847-2858`).
   Reachable only through adoption-planted/dirty storage — same threat class the
   short-form check already guards.

**Ranked NEW acceptance-soundness findings (repo accepts a program solc
rejects — matters if `importedContractAccepted` is read as a certificate):**

6. **A1 — implicit `uintN → intM` accepted** (CONFIRMED). solc forbids *all*
   signed↔unsigned implicit conversions (`Types.cpp:611`); the repo accepts
   `uintN→intM` when `N<M` (`TypeCheck.lean:1060-1061`). Rides the general
   assignment/argument predicate, so broadly reachable.
7. **A2 — mixed-sign common type** (`uint8 + int16` → `int16`) accepted
   (CONFIRMED; cascades from A1). solc returns no common type here
   (`Types.cpp:286-296`); repo `TypeCheck.lean:3218-3222`.
8. **A3 — explicit signed-int ↔ `bytesN` accepted** (CONFIRMED). solc requires
   the integer be *unsigned* in both directions (`Types.cpp:638-639,1364-1365`);
   repo tests only width (`TypeCheck.lean:1138-1141`, used at `:1396,1410,1420`).
9. **A4 — explicit contract *base→derived* accepted** (CONFIRMED). solc allows
   only derived→base (`Types.cpp:1468-1499`); repo `contractsRelated` accepts
   either direction (`TypeCheck.lean:1170-1173, 1426-1428`).

The doc is committed to `codex/solidity-semantics-only`.

---

## Soundness-risk findings (value / wrong-observable) — highest priority

### S1 — Regular string literal lowered to codepoints, not UTF-8 — NEW, CONFIRMED, HIGH
- **solc:** `liblangutil/Scanner.cpp:786-793` decodes `\u` escapes in *ordinary*
  string literals via `addUnicodeAsUTF8`, so the stored literal value is its
  UTF-8 byte sequence; `Types.cpp:1286` uses that byte length for `bytesN` fit.
- **Behavior:** `"é"` (U+00E9) is 2 bytes `0xC3 0xA9`; `bytes2("é") ==
  0xc3a9`; `bytes(s).length == 2`.
- **Repo — WRONG:** `Interface.lean:3476-3478` (`Literal.toCoreExpr?`) lowers
  `Literal.string text` to `Expr.byteArray (text.toList.map Char.toNat)` —
  **codepoints**. Same bug in the `bytesN` path `Literal.toFixedBytesWord?`
  (`Interface.lean:2988-2989`). Contrast the *correct* `unicodeString` case
  immediately below (`:3480-3481`, uses `stringUtf8Bytes`).
- **Observable:** for any regular literal with a non-ASCII char, wrong runtime
  bytes, wrong `bytes(s).length`, wrong `bytesN` value, and wrong
  `keccak256`/`abi.encodePacked` hash. Codepoints > 0xFF (`"ሴ"`) give an
  even more corrupt list. `toCoreExpr?` is the primary literal path
  (`Interface.lean:3711`), so broadly reachable.
- **Severity:** SOUNDNESS. **ALREADY-KNOWN?** No — the prior "unicode/hex-string
  literals SUPPORTED" row covers the `unicode"..."`/hex paths, which are correct;
  this is the plain-string path. NEW.
- **Probe to confirm:** compile+run `keccak256(bytes("é"))` and
  `bytes("é").length` under pinned solc vs the interpreter.

### S2 — Calldata narrow-int/enum element cleanup deferred (lazy) vs solc eager decode-time validation — NEW, CONFIRMED
- **solc:** `ABIFunctions.cpp:1106-1132` validates each value type at decode with
  `validatorFunction(_type, revertOnFailure=true)` → `revert(0,0)`; array/tuple
  decode validates *every element* the same way (`:1221`), eagerly, before the
  function body runs.
- **Repo:** external entry uses the *lazy* decoder `decodeFunctionArgs?`
  (`ABI.lean:446-452`, used at `ABI.lean:684,928`). Top-level scalars *are*
  eager-checked (`Interpreter.lean:5062-5066`), and nested `bool`/`address`/
  `bytesN` keep their `Ty` and are eager-validated (`ABI.lean:321-367`). But
  **narrow `uintN`/`intN` and `enum` lower to `uint256`**, so their
  array/tuple/struct *elements* route through `AbiCleanup.lazyValue`
  (`Interpreter.lean:5024`) into `Value.abiLazy` with no accepts-check; the raw
  256-bit word is read unvalidated (`ABI.lean:333-338`) and validation is
  deferred to first use (`Interpreter.lean:346-356`).
- **Observable:** `function f(uint8[] calldata a) external { emit E(); }` invoked
  with a dirty-high-bits element — solc reverts empty at entry (no event); the
  repo emits the event and returns success (element never forced). Same divergence
  for any dirty narrow element used only after a side effect.
- **Severity:** SOUNDNESS (success / late-revert vs eager empty revert). NEW.
  Note **F2 (dead code):** the solc-faithful eager decoder
  `decodeFunctionArgsStrict?` (`ABI.lean:454-460`) already exists but has no call
  site; switching the two external entries to it would close this.
- **Probe:** hand-craft calldata for a `uint8[]`/enum-array external fn with a
  dirty element used only after an `emit`; compare entry-revert vs success.

### S3 — Ternary in `abi.encodePacked` uses then-branch type, not common type — NEW, CONFIRMED
- **solc:** `TypeChecker.cpp:1382` types a conditional as
  `commonType(trueType, falseType)`, so `c ? aUint8 : bUint256` is `uint256` →
  32 packed bytes.
- **Repo — WRONG (interpreter width path):** `Expr.abiTy?` returns the
  then-branch type for a ternary (`Interface.lean:4818`), feeding
  `Ty.packedTopWidth` (`:3258-3266`). Yet `TypeCheck.lean:6882-6887` computes the
  *correct* common type — so the program type-checks as `uint256` but packs using
  `uint8` (1 byte) when the then-branch is narrower.
- **Observable:** `keccak256(abi.encodePacked(c ? aUint8 : bUint256))` — wrong
  hash when then-branch is the narrower type (correct when it's wider —
  order-dependent). The analogous binary-arithmetic case (`:4817`) is *not* a bug
  (solc pre-unifies both operands).
- **Severity:** SOUNDNESS (wrong bytes/hash). NEW. Related to but distinct from
  W1 (W1 loses width for *all* narrow packs; this is a ternary type-selection
  bug that persists independent of W1's fix).

### S4 — `Panic(0x41)` oversized allocation dead on production path; wrong threshold — NEW, INFERRED
- **solc:** `ExpressionCompiler.cpp:1261-1268` — `new T[](len)` panics
  `ResourceError` (0x41) when `len > 0xffffffffffffffff` (fixed 2^64-1); ~10
  further alloc/resize/copy sites in `YulUtilFunctions.cpp` share the code.
- **Repo:** `Context.checkMemoryAllocation` (`Interpreter.lean:1662-1671`) panics
  0x41 only when `memoryAllocationLimit?` is `some limit` and `size > limit`
  (call sites `:6391` `new bytes`, `:6398` `new T[]`). But the field defaults to
  `none` (`:1634,1659`) and every production context is `Context.empty`
  (`Interface.lean:18007, 19987`); the limit is `some 3` **only** in hand-built
  witnesses. So a real contract's `new bytes(2**256-1)` returns a giant list and
  never panics; and where a limit *is* set the threshold is arbitrary, not
  solc's fixed 2^64-1.
- **Severity:** SOUNDNESS (missing panic → success where solc reverts) +
  COMPLETENESS (threshold). Partly **contradicts** `docs/bc-soundness-audit.md`
  §B7's "0x41 PARITY (exact)", which only held inside limit-configured witnesses.
  NEW.
- **Probe:** run `new uint[](2**64)` and `new bytes(2**256-1)` in a normal
  contract; expect solc Panic(0x41), repo currently succeeds.

### S5 — `Panic(0x22)` long-form storage byte-array under-length not raised — NEW, INFERRED
- **solc:** `YulUtilFunctions.cpp:1360-1379` `extract_byte_array_length`:
  `if eq(outOfPlaceEncoding, lt(length, 32)) { panic StorageEncodingError }` —
  for the long form (odd low bit) it panics when decoded `length < 32`.
- **Repo:** `storageBytesHeader?` (`Interpreter.lean:2847-2858`) models only the
  **short**-form panic (`:2856`); the odd/long branch (`:2857-2858`) computes
  `(raw-1)/2` and never panics. A slot word with the low bit set and length `< 32`
  (e.g. `1`→len 0, `3`→len 1) makes solc panic 0x22 but the repo reads it as a
  valid array.
- **Severity:** SOUNDNESS. Reachable only via adoption-planted/dirty storage —
  the same narrow class the short-form check already covers. NEW.

---

## Acceptance-soundness findings (repo accepts what solc rejects)

These matter only if `importedContractAccepted` / typecheck-acceptedness is read
as a certificate; on a solc-validated corpus they never fire. All CONFIRMED.

### A1 — Implicit `uintN → intM` accepted — NEW, CONFIRMED
- **solc:** `IntegerType::isImplicitlyConvertibleTo` (`Types.cpp:605-617`) returns
  false whenever `isSigned() != convertTo.isSigned()` (`:611`) — no signed↔unsigned
  implicit conversion, any width.
- **Repo:** `Ty.canImplicitlyConvert` (`TypeCheck.lean:1060-1061`) accepts
  `uint actualBits → int expectedBits` when `actualBits < expectedBits`. This is
  the general assignment/argument predicate (`TypeCheck.lean:2038,8011,8105,…`),
  so it fires on typed variables, not just literals. `int→uint` has no branch
  (correctly rejected).
- **Severity:** SOUNDNESS (over-accept). NEW.

### A2 — Mixed-sign common type accepted — NEW, CONFIRMED (cascades from A1)
- **solc:** `Type::commonType` (`Types.cpp:286-296`) returns nullptr for
  `(uint8, int16)` → `uint8Var + int16Var` is a type error.
- **Repo:** `Ty.commonImplicit?` fallback (`TypeCheck.lean:3218-3222`) calls
  `canImplicitlyConvert` both ways → `commonImplicit?(uint8,int16) = int16`,
  accepting the binary op.
- **Severity:** SOUNDNESS (over-accept). NEW.

### A3 — Explicit signed-int ↔ `bytesN` accepted — NEW, CONFIRMED
- **solc:** `int→bytesN` needs `!isSigned() && numBits==numBytes*8`
  (`Types.cpp:638-639`); `bytesN→int` needs `!integerType->isSigned() && …`
  (`:1364-1365`). Signed rejected both ways.
- **Repo:** `Ty.fixedBytesIntegerSameSize` (`TypeCheck.lean:1138-1141`) tests only
  `size*8 == bits`, ignoring signedness; used at `:1396,1410,1420`. So
  `int8(bytes1Var)` / `bytes1(int8Var)` are accepted.
- **Severity:** SOUNDNESS (over-accept). NEW facet — `docs/bc-soundness-audit.md`
  §B4's "bytesN↔intN parity" measured only unsigned round-trip *values*, not the
  signed accept boundary.

### A4 — Explicit contract base→derived accepted — NEW, CONFIRMED
- **solc:** `ContractType::isExplicitlyConvertibleTo` (`Types.cpp:1491-1499`)
  delegates to the implicit rule (`:1468-1488`), which only succeeds when the
  target is in the source's `linearizedBaseContracts` — derived→base or identity
  only.
- **Repo:** `contractsRelated` (`TypeCheck.lean:1170-1173`) is true if *either* is
  an ancestor of the other, used by the contract↔contract explicit branch
  (`:1426-1428`). So `Derived(baseInstance)` is accepted; solc requires routing
  through `address`.
- **Severity:** SOUNDNESS (over-accept). NEW.

---

## Completeness findings (repo over-accepts/over-rejects harmlessly on valid input)

### C1 — `string.length` over-accepted — NEW, CONFIRMED
- **solc:** `ArrayType::nativeMembers` (`Types.cpp:1928-1959`) adds `length` only
  `if (!isString())`; `s.length` on a `string` is a compile error (must use
  `bytes(s).length`).
- **Repo:** the `.length` member path (`Interface.lean:4245-4255, 4806-4808,
  9304-9308`) matches any base with an `abiTy` and emits `Expr.length`;
  `Ty.hasStorageArrayMembers` (which correctly excludes string) gates push/pop but
  is not consulted for `.length`. So `string.length` elaborates.
- **Severity:** COMPLETENESS (over-accept). NEW.

### C2 — `type(C).creationCode/runtimeCode/interfaceId` not gated on deployability — NEW, CONFIRMED
- **solc:** `Types.cpp:4271-4285` — deployable contract → `{creationCode,
  runtimeCode, name}`; non-deployable (interface/abstract) → `{interfaceId,
  name}`. `type(Interface).creationCode` and `type(Concrete).interfaceId` are
  compile errors.
- **Repo:** `Ty.typeInfoExpr?` (`Interface.lean:3450-3455`) emits
  creationCode/runtimeCode for any `Ty.user`, and `interfaceId` resolves for any
  contract (`:7530`, `:17117`) — neither consults contract kind, even though the
  importer records it (`solc_ast_to_lean_source.py:1898-1904`).
- **Severity:** COMPLETENESS (over-accept). NEW.

### C3 — `abi.encodePacked(bytes[] / string[])` accepted; solc rejects arrays-of-dynamic in packed mode — NEW, INFERRED
- **solc:** packed mode forbids arrays whose elements are dynamically sized
  (`bytes[]`, `string[]`, `T[][]`) — compile-time rejection.
- **Repo:** `abiEncodePackedArrayElement?` (`Interpreter.lean:4914-4920`) bans only
  `fixedArray`/`dynamicArray`/`tuple` elements; a `bytesCalldata` element falls
  through to the padded-32 concat case (`:4801-4805`). Genuinely nested
  `uint[][]` *is* runtime-banned; only the `bytes[]`/`string[]` element leaks
  through, producing non-solc bytes for a program solc refuses.
- **Severity:** COMPLETENESS/low-SOUNDNESS (spurious accept + non-solc bytes).
  NEW.

### C4 — Constant `%` with a negative operand over-rejected — NEW, INFERRED
- **solc** folds `-7 % 3` (sign of dividend). Repo `NumberRat.mod?`
  (`Interface.lean:2788-2794`) requires `exactNat?` of both operands, rejecting
  negative constant operands. COMPLETENESS (over-reject), not unsound. NEW.

### C5 — `bytesN.length` static type is `uint256`, should be `uint8` — NEW, CONFIRMED (benign)
- **solc:** `FixedBytesType::nativeMembers` (`Types.cpp:1408-1411`) types `.length`
  as `uint8`. Repo emits the correct *value* (`Expr.word size`) but tags the ABI
  type `uint 256` (`Interface.lean:4806-4808, 9304-9308`). Benign: N ≤ 32 and both
  ABI-encode to a 32-byte word — no observable divergence found. NEW, mis-type.

### C6 — `Panic(0x41)` unmodeled at non-`new` allocation sites — NEW, INFERRED (unreachable)
- solc raises ResourceError from array resize/copy/`push`/`concat`/`encode` sites
  (`YulUtilFunctions.cpp:1411,1591,1788,1825,2125,2240,2383,3271`); the repo checks
  only `new bytes`/`new T[]`. Needs >2^64 elements — practically unreachable.
  COMPLETENESS. NEW.

---

## Already covered / not a gap (spot-checked, confirming)

The following were read on both sides and confirmed faithful — recorded so the
reader knows the obvious things were checked:

- **Integer widening implicit** (`uint→uint`, `int→int`, `N≤M`), **explicit
  same-width-or-same-sign**, **literal→integer fitting** (negative→unsigned
  rejected, range exact, fractional never reaches), **address payable→address**,
  **`payable(...)`** gating on `isPayable()`, **function-pointer mutability
  lattice**, **bytesN widening/explicit any-width**, **address↔uint160↔bytes20
  exact-width**, **enum↔unsigned-int** — all match `Types.cpp`.
  (`TypeCheck.lean:1056-1136`, `Interface.lean:3395-3401`.)
- **Cleanup on storage read**: bool→{0,1}, address→160-bit mask, bytesN keep-high
  /zero-low, enum→deferred use-site Panic(0x21). **Top-level calldata decode** of
  bool/address/bytesN/external-fn eagerly validated → empty revert. All PARITY
  (`Interpreter.lean:440-480`, `ABI.lean:321-367`).
- **ABI head/tail** offsets for nested dynamic types, **empty dynamic
  array/bytes** (length-0 word only), **decode bounds/truncation/OOB-offset**
  revert, **calldata slice `x[a:b]`** bounds revert, **packed address=20B /
  bytesN=NB**, **external function = 24B / internal has no ABI form**, **decode
  per-element validation**, **`encodeWithSelector`/`encodeCall` dynamic args** —
  all CONFIRMED faithful (resolves several UNKNOWNs in
  `docs/solidity-feature-coverage.md`). (`ABI.lean:172-367`,
  `Interpreter.lean:4673-4775`.)
- **Panic catalogue** 0x01/0x11 (checked scoping correct)/0x12 (div AND mod, signed
  and unsigned; `INT_MIN/-1`→0x11)/0x21/0x31 (pop empty; dynamic + storage
  bytes)/0x32 (index OOB incl. bytesN)/0x51 (zero-init internal fn ptr) — all
  present and correctly coded (`Interpreter.lean:272,5185-5353,4254-4274,535-578,
  8076-8078`). Revert taxonomy (empty / `Error(string)` `0x08c379a0` /
  custom errors / custom-error-in-require) present.
- **Members**: full `block.*`/`msg.*`/`tx.*`/`abi.*`/address-member sets;
  `type(EnumT).min/max` supported (constant-folded, `Interface.lean:1202-1211`);
  `.selector`/`.address` correctly gated to external function types
  (`Interface.lean:9309-9322`); push()/push(x)/pop gated to dynamic storage.
- **Statements**: `delete` on mapping/storage-pointer/calldata correctly rejected;
  call-options `{value,salt}` on `new`, `{gas,value}` on calls, `{gas}` only on
  static/delegatecall (value excluded); try/catch Error/Panic/lowlevel/bare
  dispatch on correct selectors; unit denominations exact; blobhash/blobbasefee/
  transient routed. (`TypeCheck.lean:6271-6795`, `Interpreter.lean:7140-7192`,
  `Ast.lean:152-160`.)
- **Known WRONG-VALUE (not re-reported):** W1 encodePacked narrow-int width loss,
  W2 narrow left-shift spurious panic, W3 signed-base `**` crash — all in
  `docs/bc-soundness-audit.md`. **IN-FLIGHT:** internal-fn-pointer residue,
  member-form fn values, bare-literal-cast/enum/contract-local execution gaps.

---

## Confidence & next steps

The four acceptance-soundness over-accepts (A1–A4) and the string-literal (S1),
ternary-packed (S3) value bugs are **CONFIRMED** on both sides and each has a
one-line probe to turn into a pinned red corpus lane. S2 (lazy element cleanup),
S4 (dead 0x41), and S5 (long-form 0x22) are **CONFIRMED-code / INFERRED-observable**
— the divergent code paths are read definitively, but the exact end-to-end
observable wants a solc-vs-interpreter probe under adopted/hand-crafted calldata
or storage. Recommended lane order by pervasiveness: **S1** (any non-ASCII
literal hash) → **A1/A2** (signed/unsigned mixing rides the general predicate) →
**S3** → **S2** → **S4/S5**.
