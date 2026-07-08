# Implementation-level solc-vs-Solidus divergence review (round 6 — unexplored codegen)

**Sixth implementation-level pass.** Rounds 1–5
(`docs/solc-implementation-divergences.md`, `-2.md`, `-3.md`, `-4.md`, `-5.md`)
exhaustively covered the arithmetic / cleanup / conversion helper families, the
ABI encode+decode codec (incl. the AD1 fixed-array external-decode boundary,
REFUTED), and the analysis-pass ACCEPTANCE rules
(`Type`/`TypeChecker`/`ViewPure`/`Override`/`ControlFlow`/`ContractLevel`/
`PostType`/`Immutable`/`DeclarationType`) — **no wrong-VALUE divergence** in five
rounds. This round deliberately targets the surfaces those rounds did NOT cover:
**value-producing codegen** — function-call selector/return-data/revert-decode,
event/error topic and selector computation, the value builtins Solidus
*recomputes* (`interfaceId`, `bytes.concat`, `addmod`/`mulmod`, `type(T).min/max`,
`keccak`/precompile framing, external-fn-pointer `.selector`/`.address`), and the
calldata-slice `a[i:j]` value/bounds path.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `0743b0e`. Canonical semantics
files are `SolidCore/Solidity/*.lean`. Nothing was built or run for Solidus;
tiny accept/compile probes used the pinned `solc 0.8.35`
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`). Findings are
**CONFIRMED** (both sides read to the rule/emitted-Yul, usually + probe) or
**INFERRED** (deduced from a code trace, not built).

---

## Executive summary

**Surfaces actually read this round (code, not tests), both sides:**

- **Function-selector / event-topic0 / error-selector computation** — the canonical
  signature builder `Ty.abiCanonical?` (`Interface.lean:2417-2478`),
  `selectorFromSignature`/`Keccak.selector4` (`ABI.lean:57-61`, `Keccak.lean:196`),
  event `topic0 = keccak(canonicalSig)`, `panicSelector`/`errorSelector`
  (`ABI.lean:471-473`) ↔ solc `FunctionType::externalSignature` / `AST.cpp`
  `interfaceFunctionList`.
- **`type(T).interfaceId`** — `FunctionDecls.interfaceId?` XOR fold
  (`Interface.lean:7746-7751`), `ContractDecl.interfaceId?` (17626) and the
  interface-only `interfaceIdEnv` (17633-17644) ↔ solc
  `ContractDefinition::interfaceId()` / `interfaceFunctionList(false)`
  (`AST.cpp:280-321`) and the `!canBeDeployed()` member gate (`Types.cpp:4271-4285`).
- **Recomputed value builtins** — `addmod`/`mulmod` mod-0 → Panic 0x12
  (`Interpreter.lean:5411-5423`, `Word.lean:50-54`), `bytes.concat`/`string.concat`
  exact bytes (`Interpreter.lean:248-255`), `type(T).min/max` (`Interface.lean:3496-3508`),
  external-fn-pointer `.selector`/`.address` + `function`=bytes24 ABI layout
  (`Interface.lean:4003-4010`, `ABI.lean:172-177`, `Interpreter.lean:159-174`).
- **Calldata slices `a[i:j]`** — `Value.slice?` / `sliceListByWords?`
  (`Interpreter.lean:674-705`) + `Expr.slice` eval (`Interpreter.lean:6603-6621`)
  ↔ solc `calldata_array_index_range_access_*` (`YulUtilFunctions.cpp:2523-2539`)
  and `revertReasonIfDebugBody` (`YulUtilFunctions.cpp:4598-4636`).

**Headline: this round found the campaign's first wrong-VALUE divergence.**

- **V1 (NEW, SOUNDNESS wrong-value, DIFFERENTIALLY-LIVE, CONFIRMED)** — a
  **calldata-slice out-of-bounds** (`a[i:j]` with `i > j` or `j > a.length`) reverts
  in Solidus with **`Panic(0x32)`**, but solc reverts with **empty data
  (`revert(0,0)`)**. The observable returndata differs (36 bytes vs 0 bytes).
  Live: calldata slices are compiled by solc and modeled + corpus-exercised by
  Solidus (`entrypoint-slice-control`), but the corpus only drives **in-bounds**
  slices, so the OOB revert-data is currently **untested**.
- **A1 (NEW, COMPLETENESS wrong-reject, DIFFERENTIALLY-LIVE, INFERRED)** —
  `type(AbstractContract).interfaceId` (and `type(AbstractContract).interfaceId`
  on any non-interface non-deployable contract) is accepted+computed by solc but
  **fails to lower** in Solidus (`interfaceIdEnv` is interface-only, and
  `Ty.typeInfoExpr?` has no `interfaceId` arm), so Solidus rejects a program solc
  compiles. Internally inconsistent: the typechecker (`TypeCheck.lean:5486-5499`)
  *accepts* it.

Everything else read this round is **faithful**: selector / topic0 /
error-selector / panic-selector computation, interfaceId for *interfaces*
(matches `interfaceFunctionList(false)`), `addmod`/`mulmod` (full-precision,
mod-0 Panic 0x12), `bytes.concat`/`string.concat`, `type(T).min/max`,
external-fn-pointer members + the `function`=bytes24 ABI layout, and in-bounds
slice values.

| # | Target | Verdict | Severity | Reachability |
|---|--------|---------|----------|--------------|
| **V1** | calldata-slice OOB revert data | **Panic(0x32) vs empty `revert(0,0)`** | **SOUNDNESS (wrong value)** | **DIFFERENTIALLY-LIVE** (untested in corpus) |
| **A1** | `type(AbstractContract).interfaceId` | Solidus fails to lower → rejects | COMPLETENESS (wrong-reject) | DIFFERENTIALLY-LIVE |
| F1 | selector / topic0 / error-selector / canonical sig | faithful | — | n/a |
| F2 | `interfaceId` for interfaces | faithful (matches `interfaceFunctionList(false)`) | — | n/a |
| F3 | `addmod`/`mulmod` (mod-0, full-precision) | faithful | — | n/a |
| F4 | `bytes.concat`/`string.concat`, `type(T).min/max` | faithful | — | n/a |
| F5 | fn-pointer `.selector`/`.address`, `function`=bytes24 | faithful | — | n/a |

**NEW findings this round: 2 differentially-live (1 wrong-VALUE, 1 wrong-reject),
0 importer-masked.** V1 is the first wrong-VALUE divergence surfaced in six rounds.

---

## V1 — calldata-slice out-of-bounds reverts with Panic(0x32); solc reverts empty — SOUNDNESS (wrong value)

**Claim:** `a[i:j]` on a calldata `bytes`/`string`/`T[]` with out-of-range bounds
(`i > j`, or `j > a.length`) produces a revert whose **returndata differs**
between solc and Solidus.

### solc side — empty revert (CONFIRMED, source read)

The calldata slice accessor `calldata_array_index_range_access_*`
(`YulUtilFunctions.cpp:2523-2539`):

```
function <fn>(offset, length, startIndex, endIndex) -> offsetOut, lengthOut {
    if gt(startIndex, endIndex) { <revertSliceStartAfterEnd>() }
    if gt(endIndex, length)     { <revertSliceGreaterThanLength>() }
    ...
}
```

Both `revertSlice*` are `revertReasonIfDebugFunction("Slice ...")`. Under the
**default** revert-strings setting (`RevertStrings::Default < Debug`),
`revertReasonIfDebugBody` (`YulUtilFunctions.cpp:4598-4605`) returns literally
`revert(0, 0)` — an **empty** revert with **no returndata**, no `Error(string)`,
no `Panic`. (The `Panic(0x32)` selector is emitted only for a *regular* array
**index** access `a[i]` out of range — a different Yul helper — never for a
slice-**range** access.)

### Solidus side — Panic(0x32) (CONFIRMED, source read)

`Value.slice?` (`Interpreter.lean:689-705`) delegates to `sliceListByWords?`
(`Interpreter.lean:674-687`):

```
if start <= stop && stop <= values.length then
  Except.ok ((values.drop start).take (stop - start))
else
  Except.error RevertData.indexOutOfBounds        -- <-- wrong revert data
```

`RevertData.indexOutOfBounds := RevertData.panic 0x32` (`Interpreter.lean:296-297`).
`Expr.slice` (`Interpreter.lean:6603-6621`) binds `baseValue.slice? …` in the
`SolI` monad, so the `Except.error` becomes a revert carrying `Panic(0x32)`. At
the external boundary `Contract.encodeRevertData?` (`ABI.lean:482-497`) encodes
`RevertData.panic 0x32` as `encodeSelector panicSelector ++ <0x32 word>` — a
**36-byte** returndata (`0x4e487b71` + `0x…0032`), whereas solc returns **0**
bytes.

The bounds *predicate* is correct (`i > j` or `j > len` ⇒ revert, matching solc's
two `gt` checks) and in-bounds slice **values** are correct
(`(drop start).take (stop-start)`); the divergence is purely the **revert-data
payload**. The root cause is a name/semantics collision: Solidus reuses the
array-index-OOB constant (`Panic(0x32)`, correct for `a[i]`) for the slice-range
bounds check, which solc treats as a plain empty revert.

### Reachability — DIFFERENTIALLY-LIVE (untested in corpus)

Calldata slices are a first-class corpus feature (`entrypoint-slice-control`,
`tests/forge-harness/manifest.json:1319-…`, importer + interpreter both support
`Expr.slice`). The harness function
`slice(bytes calldata input, uint256 start, uint256 stop)` takes **dynamic**
bounds, so an OOB call is trivially constructible and its revert-data is
observable to an external caller / `try…catch` / low-level `.call`. But every
manifest entry drives only **in-bounds** slices — so the OOB revert-data is
**not currently pinned**. A differential test that calls `slice(x, 5, 100)` (or
`slice(x, 3, 1)`) and inspects returndata would flag the divergence: Forge/EVM
sees empty returndata, Solidus produces `Panic(0x32)`.

**Severity: SOUNDNESS (wrong value).** **Confidence: CONFIRMED** (both sides read
to the emitted Yul / Lean; only "built" step omitted). **NEW.**

### Suggested fix (for the sibling fix-agent, not applied here)

Route the slice-bounds failure to an **empty** revert
(`RevertData.empty`) rather than `RevertData.indexOutOfBounds`, e.g. give
`sliceListByWords?` its own `RevertData.empty` error arm (leaving `a[i]` index
access on `Panic(0x32)` untouched).

---

## A1 — `type(AbstractContract).interfaceId` fails to lower; solc accepts — COMPLETENESS (wrong-reject)

### solc side — accepts + computes (CONFIRMED, probe)

`interfaceId` is a member of `type(T)` whenever `!contract.canBeDeployed()`
(`Types.cpp:4271-4285`) — i.e. for **interfaces AND abstract contracts**.
`ContractDefinition::interfaceId()` (`AST.cpp:315-321`) XORs
`interfaceFunctionList(false)` — the selectors of the externally-visible functions
**declared directly** in the contract (the `false` = exclude inherited;
`AST.cpp:286-289`). Probe (pinned solc, `--bin` exit 0):

```solidity
abstract contract A { function foo(uint256) external virtual returns (uint256); }
contract C { function g() external pure returns (bytes4) { return type(A).interfaceId; } }
```

compiles and returns `0x2fbebd38` (= `selector("foo(uint256)")`).

### Solidus side — fails to lower (INFERRED, code trace)

`ContractDecls.interfaceIdEnv` is built via `ContractDecl.interfaceIdEntry?`
(`Interface.lean:17633-17644`), which returns `some none` for any **non-interface**
contract — abstract contracts get **no env entry**. `Expr.resolveInterfaceIds`
(`Interface.lean:7781-7787`) therefore leaves `type(A).interfaceId` as an
unresolved `Expr.member (Expr.typeName (Ty.user path)) "interfaceId"`. Lowering to
the Source AST goes `Expr.member (Expr.typeName ty) member => Ty.typeInfoExpr? ty
member` (`Interface.lean:3780-3781`), and `Ty.typeInfoExpr?`
(`Interface.lean:3480-3522`) handles `name`/`creationCode`/`runtimeCode`/`min`/
`max` but has **no `interfaceId` arm** → returns `none` → `Expr.toCore?` fails →
the enclosing function/contract fails to lower → **Solidus rejects** a program
solc compiles.

This is internally inconsistent: the (post-lowering) typechecker
`TypeCheck.lean:5486-5499` explicitly *accepts* `interfaceId` for
`interface || abstract`, but the pre-typecheck lowering never reaches it for the
abstract case. (For **interfaces** the whole path is faithful: `interfaceIdEnv`
resolves them to a `bytes4` literal — see F2.)

**Severity: COMPLETENESS (wrong-reject).** **Reachability: DIFFERENTIALLY-LIVE**
— the Python importer produces valid Lean AST; the failure is in Solidus's own
Lean lowering, not the importer. **Confidence: INFERRED** (traced end-to-end, not
built). **NEW.** Niche (requires `type(AbstractContract).interfaceId`) but real.

### Suggested fix

Include abstract contracts in `ContractDecls.interfaceIdEnv` (compute
`interfaceId?` for `isInterface || abstract`, still folding only
`directOrdinaryFunctions`, which already matches `interfaceFunctionList(false)`);
alternatively add an `interfaceId` arm to `Ty.typeInfoExpr?`.

---

## Faithful surfaces (earned negatives this round)

- **F1 — selector / topic0 / error-selector / canonical signature.**
  `Ty.abiCanonical?` (`Interface.lean:2417-2478`) canonicalizes exactly as solc:
  `uint`/`int` with `bits==0`→`uint256`/`int256`, else `uint<bits>` when
  `bits%8==0 && bits<=256`; `enum`→`uint8`; `Ty.user` (contract/interface)→
  `address`; struct/tuple→`(t1,…,tn)`; fixed/dynamic arrays→`base[N]`/`base[]`;
  external `function`→`"function"`. `selectorFromSignature` = `Keccak.selector4`
  (top 4 bytes of keccak; example-pinned `transfer`/`balanceOf`/`set` at
  `Keccak.lean:202-209`). Event `topic0 = keccak(canonicalSig)` and indexed
  dynamic/reference args → `keccak` of the ABI encoding — confirmed
  corpus-green (`EventIndexedDynamic`, manifest `Blob`/`Composite`/`Fixed`:
  indexed `bytes`/`string`/`uint8[]`/`(uint8,uint16)`/`uint8[2]`).
  `panicSelector=0x4e487b71`, `errorSelector=0x08c379a0` (`ABI.lean:471-473`) —
  correct. Custom-error revert data = `encodeSelector decl.selector ++ payload`
  (`ABI.lean:497`) — matches `abi.encodeWithSelector`.
- **F2 — `interfaceId` for interfaces.** `ContractDecl.interfaceId?` folds
  `directOrdinaryFunctions` (direct, not inherited) with `xorWord`
  (`Interface.lean:7746-7751`, `17626-7631`) — **exactly** solc's
  `interfaceFunctionList(false)` XOR (`AST.cpp:315-321`). (Interfaces cannot have
  state variables, so the getter branch of `interfaceFunctionList` is vacuous.)
- **F3 — `addmod`/`mulmod`.** `checkedAddMod`/`checkedMulMod` panic `0x12` on
  mod 0 (`Interpreter.lean:5411-5423`) — matches solc's division-by-zero Panic;
  otherwise `addmodWord`/`mulmodWord` = full-precision EVM `ADDMOD`/`MULMOD`
  (`Word.lean:50-54`, no intermediate 2^256 wrap).
- **F4 — `bytes.concat`/`string.concat` + `type(T).min/max`.** `concatBytes?`
  concatenates each arg's `asBytes?` in order (`Interpreter.lean:248-255`) — exact
  bytes, no padding. `min`/`max` lower to `2^(bits-1)` signed / `2^bits-1`
  unsigned literals (`Interface.lean:3480-3508`).
- **F5 — external-fn-pointer members + `function` ABI layout.**
  `.selector`/`.address` lower to `externalFunctionSelector`/`Address`
  (`Interface.lean:4003-4010`); the packed storage word is
  `address*2^32 + selector` (`Interpreter.lean:159-174`); ABI-encodes as 20-byte
  address ++ 4-byte selector ++ 8 zero bytes = left-aligned `bytes24` in a word
  (`ABI.lean:172-177`) — matches solc's `function` external-ABI type.

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] Function-selector / event-topic0 / error-selector / panic-selector /
  canonical-signature computation — **FAITHFUL** (F1; event indexed-dynamic
  corpus-green)
- [x] `type(T).interfaceId` — **FAITHFUL for interfaces** (F2); **wrong-reject for
  abstract contracts** (A1, NEW)
- [x] Calldata slice `a[i:j]` values + bounds — **in-bounds FAITHFUL**;
  **OOB revert-data WRONG-VALUE** (V1, NEW)
- [x] `addmod`/`mulmod` mod-0 + full precision — **FAITHFUL** (F3)
- [x] `bytes.concat`/`string.concat`, `type(T).min/max` — **FAITHFUL** (F4)
- [x] External-fn-pointer `.selector`/`.address` + `function`=bytes24 ABI — **FAITHFUL** (F5)
- [x] Custom-error / panic / `Error(string)` revert encoding — **FAITHFUL** (F1)

**Still NOT reached (worklist for a future pass):**

- `type(C).creationCode`/`runtimeCode` **concrete bytes** — Solidus models these
  as opaque byte arrays (`Expr.contractCreationCode`/`RuntimeCode`); solc emits the
  actual init/runtime bytecode. Value-level fidelity of the *bytes* is out of scope
  for an open-world value semantics (no Solidity-observable value depends on the
  exact bytecode except `.length`/hashing), but not independently confirmed here.
- Precompile *result* values (`sha256`/`ripemd160`/`ecrecover`/modexp/ec-ops/
  blake2f/point-eval) — responder-answered in the open-world model (staticcall
  Query nodes, `Interpreter.lean:2299-2320`); Solidus's own **input framing** to
  the precompile (`Precompile.ecrecoverInput`, kind mapping) was spot-checked but
  the full modexp/ec-pairing input encodings were not traced this round.
- `abi.encodeCall` full type-checking of the argument tuple against the function's
  declared parameter types (selector + arg encoding traced faithful; the
  arity/type-match acceptance rule not re-examined).
- `blockhash`/`blobhash` window semantics (responder-answered; window-bound
  acceptance not re-examined).

---

## Bottom line

The sixth pass turned to the least-explored surface — value-producing codegen —
and found the campaign's **first wrong-VALUE divergence**: **V1**, a
calldata-slice out-of-bounds revert that Solidus reports as `Panic(0x32)` while
solc reverts with **empty** returndata (`revert(0,0)`). It is
**differentially-live** (slices are compiled by solc and corpus-modeled by
Solidus) but currently **untested** (the corpus drives only in-bounds slices). A
second finding, **A1**, is a differentially-live **wrong-reject**:
`type(AbstractContract).interfaceId` compiles under solc but fails to lower in
Solidus (interface-only `interfaceIdEnv` + missing `Ty.typeInfoExpr?` arm),
despite the typechecker accepting it. Every other value-producing surface read —
selector / topic0 / error-selector computation, `interfaceId` for interfaces,
`addmod`/`mulmod`, `bytes.concat`/`string.concat`, `type(T).min/max`, and
external-fn-pointer members / `function` ABI layout — is **faithful**.

**NEW divergences this round: 2 differentially-live (1 SOUNDNESS wrong-value,
1 COMPLETENESS wrong-reject), 0 importer-masked.**
