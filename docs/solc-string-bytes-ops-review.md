# solc string/bytes dynamic-ops adversarial review

Scope: dynamic `string`/`bytes` operations of Solidity 0.8.35 (legacy codegen,
ABI coder v2) vs `SolidCore` semantics. Method: read solc source at
`/Users/dan/Projects/solidity-src` (pin 47b9dedd), cross-check with the pinned
binary `solc-0.8.35`, reason through `SolidCore/Solidity/{Interface,TypeCheck,
Interpreter}.lean`. Reviewer did not modify any Lean/fixture/test.

---

## Finding 1 (CONFIRMED, over-accept) — `bytes.concat(<string variable>)` accepted; solc rejects

### Severity: medium (acceptance-boundary divergence — model compiles+executes a
program solc rejects at type-check). Confidence: high.

### Minimal repro
```solidity
pragma solidity 0.8.35;
contract C {
  function f(string memory s) public pure returns (bytes memory) {
    return bytes.concat(s);   // s is a string *variable*
  }
}
```

### solc behavior (verified against pinned binary)
Rejected at type-check:
```
Error: Invalid type for argument in the bytes.concat function call.
bytes or fixed bytes type is required, but string memory provided.
```
Legal-path evidence — `libsolidity/analysis/TypeChecker.cpp:2378-2393`
(`typeCheckBytesConcatFunction`): an argument is valid only when it is
implicitly convertible to `bytes32` **or** to `bytes memory` (and is not a
rational-number literal). A `string memory` array is implicitly convertible to
neither (`ArrayType::isImplicitlyConvertibleTo` does not allow `string`→`bytes`),
so it is rejected. A string **literal** (`StringLiteralType`) *is* convertible to
both, so `bytes.concat("abc")` is accepted — I verified `bytes.concat("abc")`
and `bytes.concat(bytes4)` both compile. The rejection is specifically for
`string`-typed **values** (variables / calldata / return values).

### SolidCore behavior — accepts and executes
Root cause: the concat-argument predicate treats `Ty.string` as a valid
`bytes.concat` argument.

- `Ty.isBytesConcatArg` — `SolidCore/Solidity/Interface.lean:3797-3802`:
  ```
  | Ty.bytes => true
  | Ty.string => true          -- <-- accepts any string value
  | Ty.bytesN size => 0 < size && size <= 32
  | Ty.fixedBytes size => 0 < size && size <= 32
  ```
- Type-checker gate uses it: `checkBytesConcatArgs`
  (`SolidCore/Solidity/TypeCheck.lean:4365-4370`) calls
  `Ty.isBytesConcatArg expr.ty`, reached from the `bytes.concat` member-call arm
  at `TypeCheck.lean:6118-6124`. A `string memory` argument has
  `expr.ty = Ty.string`, so the check passes.
- Lowering then succeeds: `Interface.lean:4506-4513` — `Tys.allBytesConcatArgs`
  is `true` for `[Ty.string]`, so the call lowers to `abiEncodePacked`, and the
  interpreter executes it (packing the string's raw UTF-8 bytes, no length
  prefix).

Net: SolidCore compiles and runs `bytes.concat(stringVariable)` returning the
raw string bytes; solc refuses to compile it.

### Why the asymmetry can't be captured by type alone
This frontend types both string **literals** and string **variables** as
`Ty.string` (`Literal.abiTy? : Literal.string _ => some Ty.string`,
`Interface.lean:3788`). solc accepts the literal but rejects the variable
(literal is `StringLiteralType`, variable is `ArrayType`). The `Ty.string => true`
arm was almost certainly added to admit the literal form (`bytes.concat("abc")`),
but because the type carries no literal/variable distinction it also admits every
string-typed value. A faithful gate would need to inspect the argument
expression (literal syntactic form) rather than only its `Ty`.

### Classification: over-accept (acceptance boundary). Not observable via the
solc differential corpus (the counterexample program is uncompilable by solc, so
it can never appear as a reference fixture) — this is exactly the class of gap
that only source review surfaces.

---

## Clean negatives (checked, agree with solc)

- **`string.concat` argument set.** `Ty.isStringConcatArg` (`Interface.lean:3808`)
  accepts only `Ty.string`; `checkStringConcatArgs` (`TypeCheck.lean:4372`)
  enforces it. solc `typeCheckStringConcatFunction`
  (`TypeChecker.cpp:2340-2364`) accepts only args implicitly convertible to
  `string memory` — i.e. `string` (and string literals, typed `Ty.string` here).
  Verified `string.concat(bytes4)` is rejected by both. Match, including the
  literal case.
- **Number-literal rejection in `bytes.concat`.** solc explicitly rejects
  rational-number literals (`TypeChecker.cpp:2384-2386`). Model: a number literal
  has `abiTy = Ty.uint 256` (`Interface.lean:3786`), which
  `isBytesConcatArg`/`isStringConcatArg` reject. Match.
- **`bytesN` packing in concat.** Both `bytes.concat` and `abi.encodePacked` pack
  a `bytesN` as its N raw bytes (no padding). `Ty.packedTopWidth`
  (`Interface.lean:3488-3496`) returns `0` (no narrow override) for `bytesN`,
  yielding the type-directed N-byte packing. `bytesN`≤32 accepted; matches
  `FixedBytesType::isImplicitlyConvertibleTo` (`Types.cpp:1352-1358`, wider-or-equal
  target ⇒ any `bytesN` converts to `bytes32`). Match.
- **Storage `bytes` short↔long boundary (push/pop, ≤31 vs ≥32).** Header
  encode/decode `storageBytesHeader?` / `storageBytesShortWord` /
  `storageBytesLongHeader` (`Interpreter.lean:2974-3011`) follow solc's
  `length*2` (short) / `length*2+1` (long) convention; malformed long-with-
  length<32 panics `0x22` (`Interpreter.lean:2986-2991`, already mined).
  `push`/`pop` (`Interpreter.lean:3134-3149`) reload the whole array, mutate,
  and re-store via `storeStorageBytesAt` (`Interpreter.lean:3076-3095`), which
  re-encodes cleanly across the boundary and clears vacated long data slots
  (`clearStorageBytesLongSlots`). Short-form store right-pads with zeros
  (`storageBytesShortWord`), so no residual dirty bytes. Vacated-byte cleanup is
  not directly observable from pure Solidity (would require assembly, out of
  scope). No divergence found.
- **Single-byte indexed read/write.** `loadStorageByteAt` /
  `storeStorageByteAt` (`Interpreter.lean:3115-3132`) address the correct
  slot/offset (`storageBytesElementSlotAndOffset`, `Interpreter.lean:3102-3113`)
  for both short and long, extract/replace exactly 8 bits, and revert
  `indexOutOfBounds` (Panic 0x32) when `index >= length`. Byte write is a
  bit-range replace preserving neighbors; `bytes1` cleanup is inherent (8-bit
  range). Match.

---

## Summary
One confirmed divergence: **`bytes.concat` over-accepts `string`-typed values**
(`Ty.isBytesConcatArg` admits `Ty.string`, `Interface.lean:3799`), which solc
rejects for anything but a string *literal*. The remaining audited surface
(`string.concat` args, number-literal rejection, `bytesN` packing, storage-bytes
short/long push/pop/index) agrees with solc.
