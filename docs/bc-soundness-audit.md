# B/C soundness audit (deferred backlog) — evidence-based

**Scope:** audit only. No semantics/checker/importer/interpreter changes. This
characterizes pinned solc 0.8.35 / Forge behavior from compiled probes, then
pinpoints where *our* executable semantics diverges, across the deferred B/C
backlog of `docs/semantic-gaps-plan.md`. Model: the A1 audit
(`docs/rational-constants-audit.md`).

**Tooling.** Probes under `tests/bc-audit-probes/` (audit artifacts, NOT wired
into `manifest.json`). Driver `tests/bc-audit-probes/drive.py`: solc `--bin`
accept/reject ground truth (pinned `solc-0.8.35`) + our import
(`scripts/solc_ast_to_lean_source.py`) + `lake env lean` `#eval` of
`CheckedInput.ownCall` witnesses. Runtime **value** ground truth from Forge
(`/Users/dan/.foundry/bin/forge`) projects under `tests/bc-audit-probes/forge/`
and `tests/bc-audit-probes/_forge/`, and hand-computed EVM values where the spec
is unambiguous.

**Classification (priority order):** WRONG-VALUE (both accept, different
observable result — highest) > OVER-ACCEPT (we accept, solc rejects) >
OVER-REJECT (we reject, solc accepts — record, don't chase) > PARITY.

---

## Ranked findings summary

### WRONG-VALUE (unsound) — hunt these hardest

| # | Area | Finding | solc/EVM | ours | reproducer |
|---|------|---------|----------|------|-----------|
| **W1** | B5 ABI | **`abi.encodePacked` pads narrow `uintN`/`intN`/`enum` to 32 bytes instead of N/8** — corrupts every `keccak256(abi.encodePacked(...))` hash (mapping keys, signed digests, Merkle leaves) | `encodePacked(uint8 12,uint8 34)` = `0x1234` (2 B) | 64 B (32-pad each) | `b5-abi/Packed.sol`, `_forge/test/Packed.t.sol` |
| **W2** | B3 arith | **narrow left-shift raises a spurious overflow panic** — Solidity shifts truncate (no overflow check even when checked); we apply a checked cleanup to the shift result | `int8(64)<<1` = `-128`; `uint8(255)<<1` = `254` | **panic 0x11** (both) | `b3-int-arith/Arith.sol` (`shlWrapSigned`,`shlTruncUnsigned`), `forge/test/Edge.t.sol` |
| **W3** | B3 arith | **signed-base exponentiation crashes** — `applySignedWord` has no `exp` case, so a signed base reverts with the internal `typeMismatch` sentinel (`panic 0`) | `(-2)**2` = `4`; `(-2)**3` = `-8` | **internal revert (panic 0)** | `b3-int-arith/Arith.sol` (`negBaseEven`,`negBaseOdd`), `forge/test/Edge.t.sol` |

All three are Forge-confirmed against pinned solc 0.8.35.

### OVER-ACCEPT (acceptance-unsound)
None found. Fixed-point (B2) is fail-closed on every operation; ABI/conversion
accept boundaries match solc.

### OVER-REJECT / execution-completeness (record, don't chase)
- B4: bare-literal casts (`uint8(200)`), enum conversions, and contract-typed
  locals typecheck-accept but fail the checked executable translation
  (`toCore?` returns `none`). Not unsound (no wrong value; the program simply
  can't be run in-model). See §B4.
- B1: side-effecting-subexpression probes accept but hit an execution gap.
- (B6/C over-rejects: see §B6/§C.)

### Fix priority (recommended)
1. **W1** — most pervasive & silent (wrong hashes flow everywhere). Carry
   bit-width to `abiEncodePackedValue?` instead of collapsing to `uint256`.
2. **W2** — spurious reverts on a common idiom (`x << n` on narrow types).
   Shift results must be truncated (unchecked cleanup) regardless of context.
3. **W3** — signed `**` is legal Solidity; add the `exp` case to
   `applySignedWord`.

### Lanes deserving a pinned corpus slot
- W1: `encodePacked(uint8,uint8)` keccak parity (red until width preserved).
- W2: `int8(64)<<1 == -128` and `uint8(255)<<1 == 254` (red — currently panic).
- W3: `int a=-2; a**2 == 4` (red — currently reverts).

---

## §W1 — B5 `abi.encodePacked` narrow-int width loss (WRONG-VALUE)

**solc/EVM (Forge-confirmed, `_forge/test/Packed.t.sol`, 5 passing 0.8.35
assertions):** packed encoding uses each value's *true* width — `uint8`→1 B,
`uint16`→2 B, `int8(-1)`→`0xff` (1 B), `enum`→1 B. Only `bytesN`, `bool`,
`address`, `string`/`bytes` are already correct in-model.

**ours:** every `uintN`/`intN`/`enum` packs as a full 32-byte word.

| probe | solc/EVM | ours | class |
|---|---|---|---|
| `encodePacked(uint8 12, uint8 34)` | `1234` (2 B) | 64 B | WRONG-VALUE |
| `encodePacked(uint16, uint24)` | 5 B | 64 B | WRONG-VALUE |
| `encodePacked(int8(-1))` | `ff` | 32×`ff` | WRONG-VALUE |
| `encodePacked(uint32)` | 4 B | 32 B | WRONG-VALUE |
| `encodePacked(enum E.C)` | `02` | 32 B | WRONG-VALUE |
| `encodePacked(bytesN/bool/address/string)` | width-correct | width-correct | PARITY |
| `abi.encode(uint8,uint16)` (32-pad both) | 2 words | 2 words | PARITY |
| nested dynamic array in `encodePacked` | REJECT | REJECT (import) | PARITY (no over-accept) |

**Root cause (file:line).** `Ty.toCore?`
(`SolidCore/Solidity/Interface.lean:2062-2073`) lowers `Ty.uint bits →
Source.Ty.uint256`, `Ty.int bits → int256`, `Ty.enum → uint256`, discarding the
bit-width. `Source.Ty` (`Interpreter.lean:68-78`) has no narrow-int constructor,
so `abiEncodePackedValue?` (`Interpreter.lean:4239-4240`) emits 32 bytes for
every int/uint. The *signature* path (`abiCanonical?`, `TypeCheck.lean:915-928`
→ topic0/selector) keeps widths correctly, so only runtime value-packing is hit.
`abi.encode` legitimately pads to 32 B, so only the `abiEncodePacked` lowering
needs the width.

Probes: `b5-abi/Packed.sol`, `b5-abi/Extra.sol`, `b5-abi/NestedPacked.sol`.

---

## §W2 — B3 narrow left-shift spurious overflow panic (WRONG-VALUE)

Solidity shift operators **truncate** the result to the left operand's type and
are **never overflow-checked**, even inside a checked block. Our lowering wraps
the shift result in the same checked `uintCleanup`/`intCleanup` used for +,−,*,
so a shift that overflows the narrow type reverts instead of truncating.

**Forge-confirmed (`forge/test/Edge.t.sol`):** `int8(64)<<1 == -128`,
`uint8(255)<<1 == 254` — no revert.

| probe | solc/EVM | ours | class |
|---|---|---|---|
| `shlWrapSigned` `int8 a=64; a<<1` | `-128` | **panic 0x11** | WRONG-VALUE |
| `shlTruncUnsigned` `uint8 a=255; a<<1` | `254` | **panic 0x11** | WRONG-VALUE |
| `shlGeWidth` `uint256 1<<256` | `0` | `0` | PARITY |
| `sarNeg`/`sarNegOneBig`/`sarGeWidthNeg/Pos` (`>>` signed) | exact | exact | PARITY |

**Root cause (file:line).** The word-level shift is correct
(`shlWord`/`sarWord`, `Shared/Word.lean:120-129`). The bug is the *cleanup*:
`uintCleanup?`/`intCleanup?` (`Interpreter.lean:512-556`) raise
`RevertData.overflow` when `checked && out-of-range`, and the importer applies a
checked cleanup to shift results via `Ty.implicitCleanupCore`
(`Interface.lean:3168-3189`; plain-binary lowering at `Interface.lean:4278-4282`
emits a bare `Source.Expr.binary` that the enclosing typed context then cleans
checked). Fix: shift results must use a truncating (unchecked) cleanup, or the
shift op should self-truncate to the operand width so the cleanup is a no-op.
`>>` never overflows (magnitude non-increasing), so only `<<` is affected.

---

## §W3 — B3 signed-base exponentiation crash (WRONG-VALUE)

Signed `**` with a signed base is legal Solidity (`int a=-2; a**2` → `4`). Our
signed-word arithmetic has no exponentiation case, so it reverts with the
internal `typeMismatch` sentinel (surfaced as `panic 0`).

**Forge-confirmed (`forge/test/Edge.t.sol`):** `(-2)**2 == 4`, `(-2)**3 == -8`.

| probe | solc/EVM | ours | class |
|---|---|---|---|
| `negBaseEven` `int a=-2; a**2` | `4` | **revert panic 0** | WRONG-VALUE |
| `negBaseOdd` `int a=-2; a**3` | `-8` | **revert panic 0** | WRONG-VALUE |
| `zeroPowZero` `0**0` (uint) | `1` | `1` | PARITY |
| `powRightAssoc` `2**3**2` | `512` | `512` | PARITY |
| `uncheckedPow256` `2**256` unchecked | `0` | `0` | PARITY |

**Root cause (file:line).** `BinaryOp.applySignedWord`
(`Interpreter.lean:4663-4708`) matches add/sub/mul/div/mod/bit/shift/compare but
has **no `BinaryOp.exp` case**, so it falls to `| _ => Except.error
RevertData.typeMismatch` (`Interpreter.lean:4708`; `typeMismatch → panic 0` at
`:251`). Fix: add a signed `exp` arm calling the existing `checkedExp` with the
signed base semantics (negative-base powers, checked overflow at result width).

---

## §B2 — fixed-point (`fixed`/`ufixed`): PARITY (fail-closed)

**solc 0.8.35 rejects essentially every fixed-point *operation*** with
`Error: Fixed point types not implemented.` (declarations of `fixed`/`ufixed`
state vars, mapping keys, and unused locals compile; any use in an expression
does not). Our checker matches: every probed operation is rejected, via the
`requireNoFixedPointValue`/`requireNoFixedPointAssignment` guards
(`TypeCheck.lean:581-588`, applied at assignment/read/conversion/parameter
binding) plus the existing 9 `fixed-point-boundary/invalid/*` cases.

| probe | solc | ours | class |
|---|---|---|---|
| `a == b`, `a < b` (compare → bool) | REJECT | REJECT | PARITY |
| `a * b` (in a bool compare) | REJECT | REJECT | PARITY |
| `-a` (unary) | REJECT | REJECT | PARITY |
| `uint256(a)` (convert out) | REJECT | REJECT | PARITY |
| `rates[a]` (fixed mapping key) | REJECT | REJECT | PARITY |
| `g(a)` (fixed as argument) | REJECT | REJECT | PARITY |
| existing invalid set (arith/bits/decimals/implicit/literal/local/getter/state) | REJECT | REJECT | PARITY |

**No over-accept found.** The comparison→bool and mapping-key→uint paths (which
could have dodged the fixed-point guards by producing a non-fixed result) are
still rejected. Probes: `b2-fixed/Fp*.sol`.

---

## §B3 — integer arithmetic edges

Beyond the three WRONG-VALUE findings above (W2 shift, W3 signed exp), every
other B3 boundary is PARITY:

| probe | solc/EVM | ours | class |
|---|---|---|---|
| `int8.min / -1` (checked) | panic 0x11 | panic 0x11 | PARITY |
| `-int8.min` (checked) | panic 0x11 | panic 0x11 | PARITY |
| `int8.min / -1` (unchecked) | `-128` | `-128` | PARITY |
| `int256.min % -1` | `0` (no panic) | `0` | PARITY |
| `-7 / 2` (trunc toward 0) | `-3` | `-3` | PARITY |
| `-7 % 3` / `7 % -3` / `-7 % -3` (sign of dividend) | `-1`/`1`/`-1` | `-1`/`1`/`-1` | PARITY |
| uint8 `255+1`/`255*2` checked | panic 0x11 | panic 0x11 | PARITY |
| int8 `100+100` checked | panic 0x11 | panic 0x11 | PARITY |
| uint8 `255+1`/`255*2` unchecked | `0`/`254` | `0`/`254` | PARITY |
| **nested intermediate overflow** `uint8: 200+100-100` (final fits, inner overflows) | panic 0x11 | **panic 0x11** | PARITY |
| int8 `100+100-100` intermediate overflow | panic 0x11 | panic 0x11 | PARITY |
| uint8 unchecked chain `200+100-100` | `200` | `200` | PARITY |
| `uint256 1<<256`, `5>>256` | `0` | `0` | PARITY |
| `-1>>255`, `-1>>256` (sign-fill) | `-1` | `-1` | PARITY |
| `int8(uint8 200)` reinterpret | `-56` | `-56` | PARITY |
| `uint8(257)` truncate | `1` | `1` | PARITY |

Notably, **narrow-type checked-overflow is enforced at each sub-operation** (the
importer inserts `uintCleanup`/`intCleanup` checked cast nodes around narrow
arithmetic), so an overflowing intermediate that later cancels still panics —
matching solc. (Initial static reading suggested this might be missed; empirical
+ Forge disproved it.) Probes: `b3-int-arith/{IntMin,Narrow,Nested,Arith}.sol`.

---

## §B4 — type conversions: PARITY (16/16 executed)

No unsoundness. Every conversion the checked interpreter can execute produces the
exact solc/EVM value. `bytesN` truncates/pads on the **right** (keeps high
bytes); `uintN`/`intN` truncate low bits (sign-extend for `intN`);
`address↔uint160↔bytes20` round-trips exact; `int8(uint8 200)=-56`,
`uint8(int8 -1)=255`, `int256(2^255)=-2^255`. Source loci:
`fixedBytesCast?`/`uintCast?`/`intCast?` (`Interpreter.lean:482/504/525`).

**Execution-completeness gaps (OVER-REJECT class, not unsound):** bare-literal
casts (`Interface.lean:3644+`), enum conversions (so the correct
out-of-range **panic 0x21** at `Interpreter.lean:4806` can't be exercised
end-to-end), and contract-typed locals — each typecheck-accepts but fails the
checked executable translation. Probes: `b4-conversions/*.sol`.

---

## §B7 — events / errors / panics: PARITY (0 divergences)

All Forge/`cast`-verified: event `topic0` = keccak of canonical signature (narrow
widths correct in the signature path); `indexed` dynamic/array types → topic =
keccak of the encoding; `indexed int8(-1)` → sign-extended 32-byte topic;
anonymous events emit no `topic0`; custom-error selectors correct; Panic codes
exact (`0x01/0x11/0x12/0x21/0x22/0x31/0x32/0x41`, `Interpreter.lean:226-251`).
`0x51` (zero-init internal fn) is unmodeled (unsupported, not unsound). Probes:
`b7-events/Events.sol`.

---

## §B1 — evaluation order (unspecified-order model)

solc 0.8.35 (legacy codegen, Forge `forge/test/Order.t.sol`) evaluates `a()+b()`
**right-to-left** (`argOrder=21003`) and `arr[i()]=v()` **value-before-index**
(`assignOrder=87`). Our model deliberately accepts *any* consistent child-eval
order (`withUnspecifiedChildEvalOrders`), so it is order-agnostic **by design** —
a differing observable for side-effecting subexpressions is not classified as
unsound here. The probes additionally hit an execution gap (internal-call-in-
expression writing storage returned an in-model error), so an exact order-value
comparison was inconclusive. Recorded, not chased. Probe: `b1-eval-order/Order.sol`.

---

## §B6 — storage packing / layout: PARITY (12/12)

No unsoundness. Every layout verified against hand-computed EVM slot words
(78-digit) and/or Forge.

| probe | result | class |
|---|---|---|
| cross-slot packing (uint8/uint16/bool/address/uint8 → 1 slot) | slot0 + all 5 getters exact | PARITY |
| partial-write masking (overwrite one field, neighbors survive) | exact masked words | PARITY |
| struct-in-array-in-struct (`Outer[3]{Inner[2] arr; tag}`) | arr/tag slots + values exact | PARITY |
| mapping-in-struct | head/m[k]/tail exact | PARITY |
| delete nested struct w/ dynamic-array field | zeroed | PARITY |
| delete array element / pop / delete mapping key | exact | PARITY |
| fixed-size array packing (`uint64[4]` → 1 slot) | exact | PARITY |
| bytesN in struct (`bytes1/bytes4/bytes32`) | exact | PARITY |
| short/long string boundary — len 30/31 (inline) | low byte = len·2; data left-aligned | PARITY |
| len 32/33 (long) | header = len·2+1; data @keccak(slot) | PARITY |

Source (all correct): `Interpreter.lean:2599-2637` (transient-aware
load/store field slot), `:2200-2225` (short/long bytes header),
`Interface.lean:17561-17635, 18494-18497` (packed layout + transient/persistent
partitioning). Probes: `b6-storage/{Packing,Nested,DeleteAgg,BytesStr}.sol`.

---

## §C — feature-coverage sweep

| probe | solc | ours | class |
|---|---|---|---|
| nested `unchecked` | REJECT (`cannot be nested`) | REJECT (same) | PARITY |
| `constant` from expression + `immutable` set in ctor | accept, exact values | accept, exact values | PARITY |
| `transient` state var (`tstore`/`tload`) | accept | accept, routed to `transient` map (verified over 3 clean runs) | PARITY |
| UDVT + `using {f as +}` operator overload | accept | accept (typecheck); exec via single-contract path → `invalidType` | ACCEPT-parity; execution gap |
| free (file-level) functions | accept | accept; exec → `unknownFunction` | ACCEPT-parity; execution gap |
| multiple inheritance / diamond (C3) | accept | accept; exec → `unknownType` (base ref) | ACCEPT-parity; execution gap |
| try/catch multiple typed clauses + `new` | accept | accept; exec → `invalidType` (`new Other`) | ACCEPT-parity; execution gap |

**3 PARITY, 4 accept-but-execution-gap.** The 4 gaps are all **accept-axis
parity** (solc-accept == our `importedContractAccepted`) that error only when
run through the single-`ContractDecl` probe entry point (`CheckedInput.ownCall`,
`Checked.lean:1206`; `ownConstruct`, `:2091`), which does not thread
cross-contract / file-level scope (base contracts, `new OtherContract`,
file-level free functions, file-level `using`-operators) into the checked call.
**None is a WRONG-VALUE or over-accept** — most likely single-contract harness
limitations rather than proven semantics unsoundness; a multi-contract execution
entry point would be needed to value-test them. If `importedContractAccepted` is
meant as a soundness certificate, the accept/execute inconsistency merits a
maintainer look. Probes: `c-features/*.sol`.

---

## Methodology caveat (CPU contention)

Probes ran alongside the main tree's long replay and sibling audit agents (load
average peaked ~90, ~40 concurrent `lean` processes). Under that load, `lake env
lean` runs were killed or, once, produced a **corrupted-but-exit-0** result (a
transient value landed in the wrong storage map) that did not reproduce on 3
clean runs. **Every PARITY above was cross-checked against exact numeric ground
truth (full slot words / Forge assertions), which corruption cannot accidentally
match; every WRONG-VALUE was Forge-confirmed against pinned solc 0.8.35.** Runs
executed during heavy contention were re-run before being trusted.
