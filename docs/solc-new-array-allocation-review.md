# `new` memory-array / bytes allocation & growth review vs solc 0.8.35 (LEGACY codegen)

Search-only divergence hunt over `new T[](n)`, `new bytes(n)`/`new string(n)`, multidim
`new`, zero-init, and the memory-limit `Panic(0x41)`. Ground truth: pinned solc 0.8.35
(legacy codegen, optimizer=false, no via_ir) + Forge. No Lean semantics were modified.

## Verdict: CLEAN NEGATIVE — no divergences found (high confidence)

Every mission point was reproduced against solc and matches solidity-lean's interpreter.
The primary concern (#3, huge-n `Panic(0x41)`) is **modeled correctly for legacy codegen**:
solidity-lean's threshold is byte-for-byte the same guard solc emits.

## Key file:line references (solidity-lean)

- `Context.checkMemoryAllocation` — `SolidCore/Solidity/Interpreter.lean:1717-1735`
  (`if size > 0xffffffffffffffff then error memoryAllocationTooLarge`).
- `Expr.newBytes` eval — `Interpreter.lean:6675-6681` (`Value.bytes (List.replicate size 0)`).
- `Expr.newDynamicArray` eval — `Interpreter.lean:6682-6691`
  (`Value.dynamicArray (List.replicate size elementTy.defaultValue)`).
- `Ty.defaultValue` — `Interpreter.lean:140-154` (recursive; `dynamicArray _ => Value.dynamicArray []`).
- `RevertData.indexOutOfBounds = panic 0x32` — `Interpreter.lean:296-297`.
- Frontend `new` translation — `Interface.lean:4355-4376`
  (`new bytes`/`new string` → `newBytes`; `T[]` dynamic → `newDynamicArray`;
  fixed-size `new uint[3]()` falls through to contract-create → `Ty.contractName?` fails → rejected).

## Key file:line references (solc, legacy path)

- `ExpressionCompiler.cpp:1255-1303` — `FunctionType::Kind::ObjectCreation` (the legacy
  `new T[](n)` / `new bytes(n)` code). The **only** overflow guard:
  ```
  m_context << u256(0xffffffffffffffff);        // 1265
  m_context << Instruction::DUP2 << Instruction::GT;
  m_context.appendConditionalPanic(PanicCode::ResourceError);   // 1268 → Panic(0x41)
  ```
  checked on the **raw requested length**. Afterward the free-memory pointer is bumped
  (`memptr + 32 + data_size`, lines 1288-1290) with **no** further overflow check, then
  zero-init runs (lines 1293-1300, skipped when length==0).

## Point-by-point

### #3 huge-n `Panic(0x41)` — the flagged item — MATCHES (high confidence)

Legacy solc panics `0x41` **iff `n > 0xffffffffffffffff` (i.e. `n >= 2^64`)** — the raw
length check at ExpressionCompiler.cpp:1265-1268. There is NO scaled free-pointer check in
legacy codegen. solidity-lean's `checkMemoryAllocation` uses exactly this bound
(`size > 0xffffffffffffffff`, `size` = the raw element/byte count). **Identical thresholds.**

Empirical (Forge, gas-capped staticcall so OOG≠panic is distinguishable):

| n (uint[]) | solc legacy | solidity-lean bound |
|---|---|---|
| 3 | ok (len 3) | ok |
| 2^59−6 … 2^64−1 | **OOG** (empty revert — genuine memory expansion) | ok (returns array) |
| 2^64 | **Panic(0x41)** | Panic(0x41) |
| 2^200 | **Panic(0x41)** | Panic(0x41) |

`new bytes(2^64)` → Panic(0x41) both sides. `new bytes(2^64-1)` → OOG (solc) — below the panic bound.

Important nuance vs the mission brief: the brief's example "`new uint[](2**59)` → 2^64 →
Panic 0x41" describes the **IR pipeline** (`finalize_allocation` in
`YulUtilFunctions.cpp:3256-3274`, which additionally panics when the *scaled* free pointer
`0x80 + 32*n + 32 > 2^64-1`, i.e. around `n≈2^59`). Under LEGACY codegen (our ground truth)
that scaled check does **not** exist: `new uint[](2**59)` runs the allocation and **runs out
of gas** during zero-init — it does NOT panic. Since OOG is pure gas metering (explicitly out
of scope) and solidity-lean matches the legacy `Panic(0x41)` threshold exactly, this is a
**clean negative**, not a divergence. (It does mean solidity-lean would *succeed* on
`new uint[](2**59)` where legacy solc OOGs, but that difference lives entirely in the
excluded gas domain — the semantic panic boundary is identical.)

The DEC-OOM abi.decode finding shares the same `checkMemoryAllocation` guard; here it is
correct for legacy, so no shared fix is needed on the `new`-array side.

### #1 zero-init + length + inner defaults — MATCHES
`new uint[](0)` → empty; `new uint[](3)` → three `0`s (`List.replicate size defaultValue`).
`new bytes[](2)` → two empty `bytes`. `new uint[][](2)` → outer length 2, each inner an
**empty length-0 array** (`Ty.defaultValue (dynamicArray _) = Value.dynamicArray []`).
solc confirmed: `a.length==2`, `a[0].length==0`; `a[0]=new uint[](3); a[0][1]=7` → 10.

### #2 `new bytes(n)` / `new string(n)` — MATCHES
Both frontend-mapped to `newBytes` → `List.replicate size 0` (zero-filled). `new bytes(4)` →
`0x00000000` in solc. `new bytes(0)`/`new string(0)` → empty.

### #4 multidim allocation depth — MATCHES
Only the OUTER array is allocated; inner arrays are default-empty (not auto-allocated) —
verified above. `new uint[2][](2)` → dynamic array of two zero `uint[2]` (fixed-array default
`fixedArray (replicate 2 (word 0))`); solc confirmed all elements 0.

### #5 assign / return / alias a new'd array — MATCHES
`uint[] memory a = new uint[](3); a[1]=5` reads back correctly; `multiWrite` (write then read)
confirmed 10 both sides. (Memory aliasing on assignment is handled by the general memory-ref
machinery, `allocMemory`/refs — unchanged by `new`.)

### #6 `new` on fixed-size array rejected — MATCHES
`new uint[3]()` is not valid Solidity; the frontend only matches `Ty.array elementTy none`
(dynamic) for `newDynamicArray` (`Interface.lean:4361`). A fixed-size `new` (`some size`)
falls to the contract-create arm, which requires `Ty.contractName?` and fails → program
rejected (no over-accept). `uint[3] memory a;` zero-inits all 3 via `Ty.defaultValue`.

### #7 memory-array has no `.push` — covered by array-copy review (not re-verified here);
memory arrays are fixed-length after allocation. Storage `.push()`/`.push(v)` zero-init also
in array-copy review.

### #8 `.length` — MATCHES
`.length` of a new'd memory array == allocation `n`; read-only for memory; `arr.length = n`
reject covered by array-copy review.

### #9 element-access bounds `Panic(0x32)` — MATCHES
`new uint[](3)` then `a[5]` → solc `Panic(0x32)` (code 50); solidity-lean
`RevertData.indexOutOfBounds = panic 0x32` (`Interpreter.lean:296, 572-607, 739-743`).

### #10 zero-init of `new S[](2)` (multi-field struct w/ dynamic member) — MATCHES
solc: `s[0].a==0`, `s[1].b==false`, `s[0].data.length==0`. solidity-lean: struct default =
`tuple` of per-field `defaultValue`, so a dynamic `bytes` member defaults to `Value.bytes []`.

## Bottom line
`new T[](hugeN)` **does** produce `Panic(0x41)` in solidity-lean, at exactly the legacy-solc
threshold `n >= 2^64`. No wrong-value / over-accept / over-reject / wrong-revert found across
all ten points. Confidence: 90% (source + empirical agreement on every case; the only
solc/solidity-lean behavioral gap is the [~2^59, 2^64) OOG band, which is out-of-scope gas).
