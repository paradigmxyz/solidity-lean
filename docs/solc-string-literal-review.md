# solc 0.8.35 vs solidity-lean: string / hex / unicode literal review

Ground truth: pinned solc 0.8.35 (`--combined-json ast`) + the Python AST importer
`scripts/solc_ast_to_lean_source.py` + Lean `SolidCore/Solidity/Interface.lean`.
Search-only; no semantics changed.

## Enforcement-location finding (where divergences *can* live)

Solidity string/hex/unicode literals are decoded **by solc, pre-import**. The
importer trusts solc's decoded AST fields:

- Regular `"..."` (kind=`string`): importer reads solc's decoded `value`
  (`solc_ast_to_lean_source.py:1063-1067`).
- `unicode"..."` (kind=`unicodeString`): reads decoded `value` (`:1073-1077`).
- `hex"..."` (kind=`hexString`): reads solc's `hexValue` hex digits (`:1068-1072`).
- Address literal: importer only produces `Literal.address` when solc already
  tagged `typeDescriptions.typeIdentifier == "t_address"` (`:1042-1047`).
- Number literal: importer copies solc's original source `value` text
  (`"0x1a"`, `"2e10"`, `"1_000_000"`, `"1.5e1"`) and Lean re-parses it.

Consequences, verified against solc:

- **Escape decoding** (`\n \t \x41 \uXXXX`, invalid-escape rejects, incomplete
  `\x4`): solc-side. solidity-lean cannot diverge on accept/reject.
- **EIP-55 address checksum** (#7): solc-side. A mis-checksummed 40-hex literal is
  rejected/typed by solc before import; the importer never re-checks. No possible
  divergence.
- **hex even-length** (#3), **adjacent literal concatenation** (#6, `"a" "b"`,
  `hex"00" hex"11"`, and mixed-kind rejects): solc-side (parse-time). solc emits a
  single already-concatenated Literal or a hard error. No divergence.
- What solidity-lean **owns**: number-literal re-parsing, the string/hex →
  `bytesN`/`bytes`/`string` **byte values and length reject**, and — critically —
  the **re-encoding of solc's decoded string `value` back into a Lean String
  literal** (`lean_string = json.dumps`, `:82-83`).

## DIVERGENCE 1 — `unicode"..."` with a non-BMP code point → wrong bytes (and over-accept)

Confidence: **95%**. Severity: **wrong-value + over-accept** (import-side root cause).

`lean_string(value) = json.dumps(value)` (`solc_ast_to_lean_source.py:82-83`) runs
with the default `ensure_ascii=True`, so every non-ASCII code point is emitted as a
`\uXXXX` escape, and every **non-BMP** code point (> U+FFFF: emoji, supplementary
planes) is emitted as a **UTF-16 surrogate pair** `😀`. Lean 4 does **not**
recombine surrogate pairs, and a lone surrogate is not a valid Unicode scalar value:
Lean parses each `\uXXXX` surrogate into a separate `Char` whose UTF-8 encoding is a
single `0x00` byte. So a non-BMP literal collapses to two null bytes.

Program:

```solidity
pragma solidity 0.8.35;
contract C {
  function f() public pure returns (bytes memory) { return bytes(unicode"😀"); }
}
```

- solc AST: `kind=unicodeString, value='😀', hexValue=f09f9880` → 4 bytes
  `[0xf0,0x9f,0x98,0x80]` = `[240,159,152,128]`.
- Importer emits `Literal.unicodeString "😀"`.
- Lean `stringUtf8Bytes` = `"😀".toUTF8.toList.map UInt8.toNat`
  evaluates to **`[0, 0]`** (2 bytes), and `"😀".length == 2`.
  (Directly evaluated with `lake env lean`.)

Downstream impact (all wrong):

- `bytes(unicode"😀").length`: solc 4, solidity-lean 2.
- `keccak256(unicode"😀")` / `abi.encodePacked`: hashes/encodes `[0,0]` not the 4 bytes.
- `bytes4(unicode"😀")`: solc = `0xf09f9880`; solidity-lean = `0x00000000`.
- **Over-accept on length:** `bytes2(unicode"😀")` — solc rejects (4 bytes > 2), but
  solidity-lean sees length 2 ≤ 2 and **accepts** with value `0x0000`
  (`Literal.toFixedBytesWord?` → `fixedBytesWordFromBytes?`, `Interface.lean:3218-3225,3187-3194`).

Root cause: `scripts/solc_ast_to_lean_source.py:83` (`json.dumps` with
`ensure_ascii=True` emitting surrogate-pair `\uXXXX`, which Lean mis-parses).

Scope: only `unicode"..."` can carry non-BMP code points (solc rejects raw non-ASCII
and lone surrogates in regular `"..."`). **BMP** non-ASCII is fine — verified
`unicode"你"` (U+4F60) → `json.dumps` `"你"` → Lean `[228,189,160]` matching solc
`hexValue=e4bda0`. ASCII control chars fine: `"\x01"` → `""` → `[1]`.

Likely **latent** (no current fixture appears to use emoji/supplementary-plane
literals) but real end-to-end in the import→Lean pipeline.

## Clean negatives (verified, with evidence)

- **#4 string/hex → `bytesN` alignment + length reject** — CORRECT for ASCII/BMP.
  `fixedBytesWordFromBytes?` (`Interface.lean:3187-3194`) left-aligns via
  `rightPadBytesTo` (`:3180-3182`) and rejects `bytes.length > size`. `bytes32("abc")`
  → `0x6162630…0`; `bytes4("abcd")` → `0x61626364`; `bytes4("abcde")` → rejected;
  `bytes4(hex"01020304")` → `0x01020304`; `bytes4(hex"0102030405")` → rejected;
  `bytes32("")` → `0x0`. (Only the non-BMP unicode input above breaks it.)
- **#7 address checksum** — solc-side; importer keys on `t_address`
  (`:1042-1047`). Mis-checksummed 40-hex literal is rejected/retyped by solc before
  import. No divergence possible.
- **#3 `hex"..."` even-length / value** — solc-side; `hexValue` is always an even
  run of hex digits. Lean `parseHexString?`/`hexDigitsToBytes?`
  (`Interface.lean:3142,3173-3178`) reproduce the byte pairs.
- **#6 adjacent concatenation** — solc-side (parse-time); a single concatenated
  Literal (or hard error for mixed kinds) is imported.
- **#1 escape sequences** — solc-side; decoded into `value`/`hexValue`.
- **#8 number forms** (`0x1a`, `2e10`, `1_000_000`, `1.5e1`, leading-zero rejects,
  precision caps) — solidity-lean re-parses solc's source text via
  `parseNumberRat?`/`parseNumberNat?` (`Interface.lean:2855-2869`); this path is the
  product of prior CE work with solc's `int32`/4096-bit precision caps replicated
  (`:2723-2768`, `:2796-2819`). Spot-checked forms parse; no divergence found.

## Coverage gap — RESOLVED 2026-07-09 (SB-A #80)

Regular `"..."` literals containing **non-UTF-8 bytes** (e.g. `"\xff"`, `"\xc3\x28"`)
make solc emit `value=null` (only `hexValue`). The importer used to `fail()` in the
`kind == "string"` branch (`"string literal missing value"`), so such valid-solc
programs were **excluded from the corpus** rather than imported.

**Fixed:** the `kind == "string"` branch now falls back to `node.get("hexValue")`
when `value` is absent/non-str, lowering the literal as `Expr.literal
(Literal.hexString <hexValue>)` — exactly like the sibling `hexString` branch.
This matches solc's boundary precisely: solc types such a literal as
`literal_string hex"..."` (the SAME type as a `hex"..."` literal), which converts
to `bytes` (ACCEPT — verified for both `bytes("\xff\x00\x41")` and `bytes memory b
= "\xff\x00\x41";`) but is NOT implicitly convertible to `string` (REJECT:
"Contains invalid UTF-8 sequence"). In Lean `Literal.hexString` has `abiTy? =
Ty.bytes`, so the checker likewise accepts the bytes contexts and rejects the
string context. Valid-UTF-8 plain string literals still carry a `value` field, so
the new branch never triggers for them (no regression). Exercised by the
`nonutf8-string-literal` harness lane (`bytes` accept + `invalid/StringNonUtf8.sol`
string reject).

## Recommendation (import-side, does not touch Lean semantics)

`lean_string` should encode solc's decoded `value` in a way that preserves the exact
UTF-8 byte sequence for non-BMP code points — e.g. `json.dumps(value,
ensure_ascii=False)` (so Lean gets the real character, whose `toUTF8` is correct), or
emit `\u{XXXXXX}` Lean escapes from the true code points instead of UTF-16 surrogate
pairs. This is the single fix for DIVERGENCE 1.
