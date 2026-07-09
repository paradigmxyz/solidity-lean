# Enum semantics review: solidity-lean vs solc 0.8.35

Ground truth: pinned solc 0.8.35 (`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`),
legacy codegen. Search-only review; no Lean semantics changed.

## Summary

- **1 divergence found** — over-reject: ordered enum comparisons (`<`, `<=`, `>`, `>=`)
  are rejected by the type checker even though solc accepts them (confidence 90%).
- **8 clean negatives** — every other rule in scope (Panic 0x21 on conversion incl.
  under `unchecked`, ABI-decode range validation, underlying width, enum→int,
  equality, arithmetic/bitwise rejection, `type(E).min/max`, packing, default value)
  matches solc.

---

## DIVERGENCE 1 — ordered enum comparison over-rejected (over-reject, 90%)

**Program**
```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
enum Color { Red, Green, Blue }
contract C {
  function lt(Color a, Color b) external pure returns (bool) { return a < b;  }
  function le(Color a, Color b) external pure returns (bool) { return a <= b; }
  function gt(Color a, Color b) external pure returns (bool) { return a > b;  }
  function ge(Color a, Color b) external pure returns (bool) { return a >= b; }
}
```

**solc result** — compiles cleanly. solc treats enums as value types with ordinal
ordering; `<`/`<=`/`>`/`>=` on same-enum operands compare the underlying ordinals and
return `bool`. Verified: the contract above compiles to bytecode with no error/warning.

**solidity-lean result** — REJECTED at type-check. The ordered-comparison branch
`TypeCheck.lean:7180-7191` calls `CheckedExprs.relationalTy`
(`TypeCheck.lean:3453-3456`), which requires `Ty.isRelationalOperand` on the common
operand type. `Ty.isRelationalOperand` (`TypeCheck.lean:408-411`) admits only
`address`, arithmetic (`uint/int/fixed/ufixed`), and fixed-bytes types — **enum is
not listed**. An enum-typed operand therefore fails `require (allowed ty)` inside
`commonCheckedTyFor` (`TypeCheck.lean` `commonCheckedTyFor`) with
`TypeError.expectedNumeric`.

Note the asymmetry: equality (`==`/`!=`) *is* enum-aware —
`Ty.isEqualityComparable` explicitly lists `Ty.enum _` and enum `Ty.user path`
(`TypeCheck.lean:3462-3477`) — but the ordered-comparison predicate omits enums.
The runtime would compare them correctly if allowed (enums are lowered to ordinal
words; word comparison at `Interpreter.lean` binary-op handling), so this is purely
a frontend over-reject, not a wrong value.

**Root cause** — `SolidCore/Solidity/TypeCheck.lean:408-411` (`Ty.isRelationalOperand`
missing the `Ty.enum _` / enum `Ty.user path` cases).

**Severity** — over-reject. Blocks common enum state-machine patterns such as
`require(state < State.Done)`.

**Confidence** — 90%. solc acceptance directly verified by compilation; the reject
path is read straight from the operand predicate and its single call site. The 10%
reserves for a build-time confirmation of the exact error (not run here to avoid a
full `lake build`); corroborated independently by a second search pass.

---

## Clean negatives (verified, match solc)

### #1 Underlying type & width — MATCH
solc **rejects enums with >256 members**: `enum Big { M0..M256 }` (257 members) →
`Error: Enum with more than 256 members is not allowed.` (verified against solc
0.8.35). So every enum has a `uint8` underlying type; there is no uint16 boundary to
get wrong. solidity-lean hard-codes uint8 accordingly: ABI source type `uint8`
(`Interface.lean:1145-1146`, `2477`, `3479-3480`), packed width 1 byte
(`Interface.lean:3483-3495`, `2212`), storage read mask `and(w, 0xff)` i.e. `% 256`
(`Interpreter.lean:498-511`). Correct.

### #2 Out-of-range int→enum → Panic 0x21, NOT suppressed by `unchecked` — MATCH
solc IR (`convert_t_uintN_to_t_enum → cleanup_t_enum → validator_assert_t_enum`):
`if iszero(lt(value, N)) { panic_error_0x21() }`. The `unchecked` body still emits
the same `convert_t_uint8_to_t_enum` call (verified in `--ir` for a function whose
body is `unchecked { Color c = Color(x); ... }`) — the range check is a distinct
check, not arithmetic overflow, so `unchecked` does not disable it.
solidity-lean: `enumFromUIntValue` (`Interpreter.lean:5765-5784`) takes **no**
`checked` flag and always range-checks → `RevertData.enumConversion = panic 0x21`
(`Interpreter.lean:287-288`); its eval site (`Interpreter.lean:6684-6688`) never
consults checked mode. Correct, incl. under `unchecked`.
Also verified: solc range-checks the **full** source word (`cleanup_t_uint256` is
identity — no pre-mask to uint8), so `Color(uint256(258))` panics rather than
wrapping to `258 & 0xff = 2`. solidity-lean's full-word `norm word <= norm maxValue`
check matches.

### #3 enum→int conversion — MATCH
`uint8(e)`/`uint(e)` returns the ordinal via the masking cast `uintCast?`
(`Interpreter.lean:633-643`), widening allowed, no range check on this direction.
Implicit enum→int is disallowed (explicit conversion required). Correct.

### #4 enum equality — MATCH (but see Divergence 1 for the ordered ops)
`==`/`!=` accepted and correct via `Ty.isEqualityComparable` (`TypeCheck.lean:3471,
3476`, enforced `7192-7210`).

### #5 enum arithmetic / bitwise rejected — MATCH
`+,-,*,/,%` → `arithmeticTy`/`Ty.isArithmeticOperand` (no enum) →
`TypeError.expectedInteger`. Bitwise → `bitwiseTy`/`Ty.isBitwiseOperand` (no enum) →
rejected. Correct over-reject matching solc.

### #6 type(E).min / type(E).max — MATCH
Folded during resolution: `type(E).min → 0`, `type(E).max → #members−1`, `E.Member →`
ordinal (`Interface.lean:1203-1217`). Correct (0.8.8+ behavior).

### #7 Storage packing — MATCH
Enum field packs at 1-byte width, offset 0, unsigned, sharing a slot with adjacent
small fields (`Interface.lean:2212`, `2303-2325`; storage lane
`StorageLayout.packedScalar 0 1 false (Ty.enumStorage maxValue)`). Read masks the
lane byte and defers range validation to use-sites (`Interpreter.lean:498-511`);
write re-checks (`Interpreter.lean:420-428`). Matches solc `cleanup_from_storage`.

### #8 ABI decode of enum param — range-validated, EMPTY revert — MATCH
solc IR: `abi_decode_t_enum → validator_revert_t_enum`:
`if iszero(lt(value, N)) { revert(0, 0) }` — an **empty revert**, NOT Panic 0x21
(verified in `--ir` for `function takeEnum(Color c)`). solidity-lean lowers enum ABI
params to `uint256 + AbiCleanup.enum maxValue` (`Interface.lean:2132-2133`), whose
`accepts` checks `norm value <= norm maxValue` (`Interpreter.lean:330-331`) and whose
`forceValue` failure returns `RevertData.empty` for plain `AbiCleanup.enum`
(`Interpreter.lean:357-367`) — the empty revert — while the storage-load variant
`AbiCleanup.enumStorage` returns Panic 0x21. This two-validator split exactly mirrors
solc `validator_revert_t_enum` (decode) vs `validator_assert_t_enum` (storage/use).
Correct. (The mission brief's phrasing "Panic/revert at the decode boundary" is
satisfied by the empty revert; solidity-lean is right to NOT emit 0x21 here.)

### #9 Default value — MATCH
Uninitialized enum = ordinal 0 (first member): `Ty.enumStorage _ → Value.word 0`
(`Interpreter.lean:154`); source-level `Ty.enum` default (`Interface.lean:6732-6735`).
Correct.

---

## Method notes
- solc acceptance/rejection verified by `solc --bin` (compile success/error).
- solc revert-vs-panic distinctions verified by reading `solc --ir` validator bodies
  (`validator_revert_t_enum` → `revert(0,0)`; `validator_assert_t_enum` →
  `panic_error_0x21`; `convert_*_to_t_enum` cleanup chain; `>256 members` diagnostic).
- solidity-lean behavior read from `SolidCore/Solidity/{Interpreter,Interface,TypeCheck}.lean`.
- No full `lake build` run; the one divergence is a frontend predicate omission read
  directly from source and its call site.
