# Implementation-level solc-vs-Solidus divergence review (round 5)

**Fifth implementation-level pass.** Rounds 1–4
(`docs/solc-implementation-divergences.md`, `-2.md`, `-3.md`, `-4.md`) read the
arithmetic / cleanup / conversion / ABI codec / storage-helper families, the
analysis-pass bodies (`ViewPureChecker`, `OverrideChecker`,
`ControlFlowAnalyzer`, `ContractLevelChecker`, `ImmutableValidator`,
`DeclarationTypeChecker`), the `using`-for legality surface, `FunctionCallOptions`
legality, the struct/nested ABI decoder, and the event/error/`abi.decode`
acceptance rules — and found **no wrong-VALUE divergence** across four rounds,
only accept/reject-boundary items (E/O/CF/PT/CL/PK/UF), most of them
importer-masked. This round has a single high-value priority — **AD1**, the
claimed fixed-array-element external-ABI-decode panic — plus the round-4
still-not-reached families (storage-size acceptance, chained call-options,
literal/escape/checksum validation, the Yul allocation sequence).

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `c5bb53b`. Canonical semantics
files are `SolidCore/Solidity/*.lean`. Nothing was built or run for Solidus; a
handful of tiny **accept/reject** probes used the pinned `solc 0.8.35` binary
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`). Findings are
**CONFIRMED** (both sides read to the rule, usually + probe) or **INFERRED**
(deduced).

---

## Executive summary

**Families / passes actually read (code, not tests), both sides:**

- **AD1 target** — solc `TypeChecker` fixed-array param acceptance + `ABIFunctions`
  `abiDecodingFunctionArray` (nested/static + dynamic-element) ↔ Solidus's
  external calldata decode boundary `Contract.callCalldataAtFromWithContext?` →
  `decodeFunctionArgs?` → `decodeArgs?` → the fixed-array arm of
  `decodeValueAtWithFuel?` (`ABI.lean:389-406`, plus `Ty.isDynamicAbi`,
  `Ty.staticAbiHeadWords?`/`abiHeadWords?`, `Ty.abiDecodeFuel` at
  `ABI.lean:81-151`).
- `TypeChecker::visit(FunctionCallOptions)` chained-`{...}{...}` rule
  (`1645_error`) ↔ importer node coverage.
- `checkStorageSize` too-much-storage (`7676`/`5026`) and
  `checkStorageLayoutSpecifier` (`7587`/`8894`) ↔ Solidus storage modelling.
- Literal validators (address checksum, `hex"…"` odd length) run in solc's
  analysis phase before AST export ↔ importer.

**Headline: NO new wrong-VALUE / wrong-ORDER soundness divergence, and the
priority target AD1 does NOT reproduce.** The fixed-array-element external ABI
calldata decoder in Solidus is **faithful** — value-correct and revert-correct —
for single-level, nested-static, and dynamic-element fixed arrays. The
single-level case (`uint8[2]` calldata) is already **differentially replay-green**
in the corpus (the `AbiMalformed` case drives it through `callCalldata`); the
nested (`uint8[2][2]`) and dynamic-element (`bytes[2]`, `uint256[][2]`) cases are
traced faithful with exactly-sufficient depth-based fuel. Every secondary target
is **solc-REJECT → importer-masked** (acceptance-oracle-only): chained call
options (1645), too-much-storage (7676/5026), bad checksum, odd-length `hex`.

**NEW findings this round: 0 differentially-live, 0 importer-masked.** This is an
earned negative, consistent with four prior rounds. The most valuable result is
the **refutation of AD1**: the highest-priority suspected soundness/completeness
gap at the external ABI boundary is confirmed **not to exist**.

| # | Target | Verdict | Reachability |
|---|--------|---------|--------------|
| **AD1** | fixed-array-element external calldata decode "panics" / over-rejects | **REFUTED — faithful** (single-level corpus-green; nested + dynamic-element traced faithful) | n/a (no divergence) |
| T2 | storage-size / storage-layout-specifier acceptance | solc rejects → **IMPORTER-MASKED**; value level faithful | acceptance-oracle-only |
| T3 | chained `f{value:}{gas:}()` (1645) | solc rejects → **IMPORTER-MASKED** | acceptance-oracle-only |
| T4 | address checksum / odd-length `hex"…"` / escapes | solc rejects pre-AST → **IMPORTER-MASKED** | acceptance-oracle-only |
| T5 | `abiDecodingFunctionStruct` FMP allocation sequence | pure Yul allocation order, invisible to value semantics → **NOT A FINDING** | n/a |

---

## AD1 characterization — REFUTED (fixed-array-element ABI decode is faithful)

**Claim under test:** calling an external function whose parameter has a
fixed-array element type (e.g. `function packMatrix(uint8[2][2] calldata)
external`) through Solidus's external-call boundary / ABI calldata decoder
*panics* (or over-rejects), though solc compiles it and the EVM decodes it.

### solc side — accepts and decodes (probe CONFIRMED)

```solidity
contract C {
  function packMatrix(uint8[2][2] calldata m) external pure returns (uint256) {
    return uint256(m[0][0]) + m[1][1];
  }
  function packFixed(uint256[3] calldata a) external pure returns (uint256) {
    return a[0] + a[2];
  }
}
```

Both compile cleanly under the pinned `solc 0.8.35` (`--bin` succeeds, exit 0);
solc emits `abi_decode_tuple_t_array$_t_uint8_$2_memory_ptr_$2_…` /
`abi_decode_available_length_…` decoders for the fixed-array params. A
fixed-array parameter (nested or not) is a fully legal external parameter.

### Solidus side — faithful (decoder read + traced; single-level corpus-green)

The external ABI boundary is `Contract.callCalldataAtFromWithContext?`
(`ABI.lean:676-684`) → `decodeFunctionArgs?` (`ABI.lean:446-452`) →
`decodeArgs? (function.params.map BindingDecl.ty) (calldata.drop selectorBytes)`
(`ABI.lean:442-444`) → `decodeArgsAux?` (`ABI.lean:433-440`) →
`decodeValueAt?`/`decodeValueAtWithFuel?` (`ABI.lean:319-431`). The importer maps
`uint8[2][2]` to `Ty.array (Ty.array … (some 2)) (some 2)`
(`scripts/solc_ast_to_lean_source.py:630-641`), which lowers to
`Ty.fixedArray 2 (Ty.fixedArray 2 Ty.uint256)`.

The **fixed-array arm** of the decoder (`ABI.lean:389-406`):

```
| fuel + 1, argData, headIndex, Ty.fixedArray size elementTy =>
    let rec decodeArrayValues? (arrayData) : Nat -> Nat -> Option (List Value)
      | 0, _ => some []
      | remaining + 1, index => do
          let value ← decodeValueAtWithFuel? fuel arrayData index elementTy
          let step  ← Ty.abiHeadWords? elementTy
          let rest  ← decodeArrayValues? arrayData remaining (index + step)
          some (value :: rest)
    if Ty.isDynamicAbi elementTy then
      let offset ← readWord? argData (wordBytes * headIndex)     -- dynamic layout
      let values ← decodeArrayValues? (argData.drop offset) size 0
      some (Value.fixedArray values)
    else
      let values ← decodeArrayValues? argData size headIndex     -- in-place static layout
      some (Value.fixedArray values)
```

This matches the ABI spec on every axis I traced:

1. **Static in-place layout (the AD1 example).** For
   `T = fixedArray 2 (fixedArray 2 uint256)`, `Ty.isDynamicAbi T = false`
   (`ABI.lean:81-86`: `fixedArray _ e → isDynamicAbi e`, `uint256 → false`), so
   the else-branch reads elements **in place** from the enclosing object with no
   offset indirection — exactly solc's in-place static-array head. The per-element
   `step = Ty.abiHeadWords? elementTy` is the multi-word static stride
   (`staticAbiHeadWords?`: `fixedArray size e → size * words(e)`,
   `ABI.lean:103-108`), so the inner `uint8[2]` elements are read at head indices
   0 and 2, and the leaves at word indices 0,1,2,3 — the correct 4-word packed
   layout. `uint256[3]` is the trivial one-level case (indices 0,1,2). Values are
   **correct**, and every read goes through `readWord?`, which returns `none`
   (→ revert) on a short buffer, matching solc's `abi_decode_available_length`
   bounds `revert`.

2. **Dynamic-element layout.** For a fixed array whose element is dynamic
   (`bytes[2]`, `uint256[][2]`, `uint256[][2][2]`), `Ty.isDynamicAbi = true`, so
   the then-branch reads the param's head **offset** word, drops to the array
   region, and decodes `size` elements whose per-element head words (`step = 1`)
   and sub-offsets are **relative to the array-region start** — exactly the ABI
   rule for a dynamic array-of-dynamic. Traced correct to depth 3.

3. **Fuel is exactly deep enough (no fuel-exhaustion over-reject).**
   `Ty.abiDecodeFuel` (`ABI.lean:141-149`) is depth-based (`fixedArray _ e →
   fuel(e)+1`), and the decoder decrements by exactly one per nesting level
   (`fuel+1` pattern, recursing with `fuel`). For `uint8[2][2]`,
   `abiDecodeFuel = 3`; the trace consumes fuel 2 → 1 → 0 and terminates with the
   correct value. Fuel counts *depth*, not element count, so arbitrarily wide
   fixed arrays decode without a spurious `none`. **There is no panic and no
   fuel-shortfall over-reject.**

### Corpus corroboration (differentially replay-green)

The `AbiMalformed` case (`tests/forge-harness/manifest.json:3995`) drives the
**exact** boundary — `CheckedContract.callCalldata 256 contract …
(selector "uint8FixedArrayFirst(uint8[2])" ++ args)` and
`"uint8FixedArraySecond(uint8[2])"` — asserting the decoded value on a clean
buffer, the empty revert on a dirty *read* element, and the lazy success on a
dirty *unread* element, all matching Forge/EVM. So the single-level
fixed-array-element calldata decode path is **differentially confirmed** (part of
the 105/105 replay-green suite). Solidus's typechecker also **accepts** nested
`uint8[2][2]` (pinned by the PK1 nested-static-array witness,
`tests/forge-harness/manifest.json:6789`). Nesting and dynamic-element variants
reuse the same recursive arm traced above.

### Verdict

**AD1 does not reproduce.** The fixed-array-element external ABI calldata decoder
is faithful — value-correct, bounds/revert-correct, and fuel-sufficient — for
single-level, nested-static, and dynamic-element fixed arrays. No panic, no
over-reject, no wrong value. **CONFIRMED negative** (decoder read end-to-end +
single-level corpus-green + solc accept/decode probe + full trace of the nested
and dynamic-element cases). This is the strongest earned negative of the AD-series
targets: the highest-priority suspected external-boundary soundness/completeness
gap is confirmed absent.

---

## T2 — storage-size / storage-layout-specifier acceptance — IMPORTER-MASKED

- **solc** `checkStorageSize` / `checkStorageLayoutSpecifier`
  (`ContractLevelChecker`/`StorageLayout`): a contract whose state variables
  exceed `2**256` slots, or a single type too large for storage, is a **compile
  error**. Probe: `uint256[2**256-1][2**256-1] x;` →
  `Error: Contract requires too much storage.` and
  `Error: Type too large for storage.` (pinned solc rejects; no `--bin`).
- **Solidus** models storage as an address-indexed word map (no `2**256`-slot
  cap surfaced at the value level; storage packing/layout is faithful — verified
  rounds 1–3 for the value semantics). The 256-slot-overflow *acceptance* rule is
  not independently modelled.
- **Reachability: IMPORTER-MASKED.** solc rejects → no AST is exported → Solidus
  never sees an over-large layout in the differential harness. Value level is
  faithful; the acceptance rule matters only to a standalone acceptance oracle.
  CONFIRMED (probe + read). Not a differential divergence.

## T3 — chained `f{value:v}{gas:g}()` (error 1645) — IMPORTER-MASKED

- **solc** `TypeChecker::visit(FunctionCallOptions)` `1645_error`: options set
  twice on one call must be combined into a single `{...}`. Probe:
  `i.f{value:1}{gas:2}()` →
  `Error: Function call options have already been set, you have to combine them
  into a single {...}-option.` (pinned solc rejects).
- **Solidus** has no chained-options arm; each `Expr.callWithOptions` arm accepts
  a single option set (round 4 §3). Because solc rejects the chained form, the
  importer never exports a doubly-nested `FunctionCallOptions` AST.
- **Reachability: IMPORTER-MASKED.** Round-4's UNTESTED corner now resolved:
  solc rejects → acceptance-oracle-only, no value divergence either way.
  CONFIRMED (probe).

## T4 — address checksum / `hex"…"` odd length / escapes — IMPORTER-MASKED

- **solc** validates address-literal checksums, `hex"…"` nibble parity, and
  `\x`/`\u` escape well-formedness in the analysis phase, **before** AST export.
  Probes (all pinned-solc rejections):
  `address a = 0xAbCdEf…;` → `Error: … invalid checksum. Correct checksummed
  address: "0xabCDeF…"`; `return hex"abc";` → `Error: Expected even number of
  hex-nibbles.`
- **Solidus** consumes solc's already-parsed literal values from the AST; it does
  not re-run source-level literal validation.
- **Reachability: IMPORTER-MASKED.** solc rejects the source → no AST → not
  independently modelled by Solidus; acceptance-oracle-only. CONFIRMED (probes).

## T5 — `abiDecodingFunctionStruct` free-memory-pointer allocation sequence — NOT A FINDING

solc's struct/array decoders bump the free-memory pointer (allocate a fresh
memory object per aggregate) in a fixed order. This is a pure **Yul
allocation-order** property, invisible to a value-level Solidity semantics: no
Solidity-observable value, revert, event, or return depends on the concrete
memory addresses chosen. Solidus reproduces the observable (values + bounds
reverts, rounds 1–2 + round 4 §4); the bump order itself is out of scope for a
value semantics and produces no divergence. **Explicitly not a finding.**

---

## Families reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] **AD1** fixed-array-element external ABI calldata decode: static in-place,
  nested static, dynamic-element layouts; head/tail offset discipline; per-element
  static stride; depth-based fuel sufficiency; bounds→revert — **FAITHFUL**
  (REFUTED; single-level corpus-green, nested/dynamic traced)
- [x] Chained `f{value:}{gas:}()` (1645) — solc rejects → **IMPORTER-MASKED**
  (round-4 UNTESTED corner resolved)
- [x] `checkStorageSize` too-much-storage (7676/5026) / storage-layout specifier
  (7587/8894) — solc rejects → **IMPORTER-MASKED**; value level faithful
- [x] Address checksum / `hex"…"` odd-length / escape validation — solc rejects
  pre-AST → **IMPORTER-MASKED**
- [x] `abiDecodingFunctionStruct` FMP allocation sequence — **NOT A FINDING**
  (pure Yul allocation order, value-invisible)

**Still NOT reached (worklist for a future pass):**

- Denomination / scientific / rational literal bound edge cases beyond the escape
  set probed here — performed by solc before AST export (importer-masked class).
- `ControlFlowRevertPruner` full algorithm (CF2 residuals) — IN-FLIGHT sibling
  arc, not re-examined.
- `using … for *` wildcard value semantics (G20) — IN-FLIGHT.
- Operator-binding over-accepts UF2/UF3 (round 4) — IN-FLIGHT sibling fix.

---

## Bottom line

The fifth pass targeted the one suspected high-value external-boundary
soundness/completeness gap (**AD1**) and the round-4 still-not-reached acceptance
families. **AD1 is refuted:** Solidus's fixed-array-element external ABI calldata
decoder is faithful for single-level (corpus-green), nested-static, and
dynamic-element fixed arrays — value-correct, revert-correct, and
fuel-sufficient. No panic, no over-reject. Every secondary target
(chained call options, too-much-storage, bad checksum / odd `hex`) is a
solc-REJECT and therefore **importer-masked** — relevant only to a standalone
acceptance oracle, never to the differential harness. The Yul allocation
sequence is value-invisible and not a finding.

**NEW divergences this round: none — 0 differentially-live, 0 importer-masked.**
This is an earned negative, extending the four prior clean-value rounds: no
wrong-VALUE or wrong-ORDER divergence anywhere touched, and the top-priority
external-ABI-boundary hypothesis confirmed absent.
