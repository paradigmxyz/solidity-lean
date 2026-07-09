# Implementation-level solc-vs-solidity-lean divergence review (round 9 — low-level `call`/`staticcall`/`delegatecall` return-data & revert bubbling)

**Ninth campaign round** (the eighth `divergences-*` doc; the plan's **Round-9**,
the highest-priority UNEXPLORED P0 surface). Rounds 1–7 mined arithmetic/cleanup,
the ABI codec, the analysis-pass acceptance rules, value-producing codegen (round 6:
V1 calldata-slice-OOB, A1 abstract-`interfaceId`), and runtime behavior (round 7:
DL1 storage/ctor order); the two memory rounds mined the memory graph (M1 family).
This round traces the surface those rounds skipped: what a caller **observes** from
a low-level or high-level external call — the `(bool ok, bytes memory ret)` pair,
the `try/catch` clause dispatch, and how a callee revert **bubbles** — the exact
V1 class the plan flagged (§3 Round-9): "a *revert-encoding / returndata*
re-derivation that can silently differ from concrete EVM".

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit `47b9dedd`,
READ-ONLY — the exact source of the pinned binary). solidity-lean at branch
`codex/solidity-semantics-only` HEAD (round-7/memory-2 tip). Canonical semantics
are `SolidCore/Solidity/*.lean`. Nothing was built/run for solidity-lean; the headline
finding is confirmed with a Forge probe against the pinned `solc 0.8.35`. Findings
are **CONFIRMED** (both sides read to the rule + Forge ground truth + solidity-lean code
trace) or **INFERRED** (code trace only).

---

## Executive summary

**Surfaces read this round (code, both sides):**

- **Low-level `call`/`staticcall`/`delegatecall` return** — solidity-lean
  `emitLowLevelCall` → `decodeCallResponse` (`Interpreter.lean:2277-2303`), returned
  as `(boolWord result.success, Value.bytes result.output)`
  (`Interpreter.lean:6403-6430`) ↔ solc's `CALL`/`STATICCALL`/`DELEGATECALL` +
  `returndatacopy`.
- **High-level call revert bubbling** — `Stmt.tryExternalCall` failure arm
  (`Interpreter.lean:8354-8401`), bubble via `RevertData.fromRawBytes output`
  (`:8401`) ↔ solc `forwardingRevertFunction` (`YulUtilFunctions.cpp:4147-4172`).
- **`try/catch` clause dispatch/decode** — `TryCatchClause.match?` /
  `findMatch?` (`Interpreter.lean:7287-7316`), Error/Panic selector gate +
  `abiDecodeValues?` decode ↔ solc `handleCatch`
  (`IRGeneratorForStatements.cpp:3460-3521`) with the purpose-built
  `returnDataSelectorFunction` / `tryDecodeErrorMessageFunction` /
  `tryDecodePanicDataFunction` (`YulUtilFunctions.cpp:4656-4762`).
- **`delegatecall` storage-write observability** — `buildCallRequest` (`recipient
  := self` for delegatecall, `:2243-2252`) + `adoptWorld` (self storage read back
  from `postWorld.accounts[self]`, `:2139-2153`).
- **Missing-code gate for high-level calls** — `missingCode := checkTargetCode &&
  !hasCode` → `LowLevelCallResult.failedRequest` (`:8335-8344`) ↔ solc's
  `extcodesize` guard on typed external calls.

**Headline: this round found one CONFIRMED soundness divergence — CB1 — in the
`try/catch` `Error(string)` clause dispatch.** solidity-lean re-derives the Error clause
match with its **strict standard ABI codec**, whereas solc gates the Error clause
behind a hard **`returndatasize() >= 0x44` (68-byte)** check in the purpose-built
`tryDecodeErrorMessage`. The two agree for every canonical `Error("…")`, but for a
callee that reverts with a short, non-canonically-framed `Error`-selector payload
(as few as 36 bytes) solc falls through to the `catch (bytes memory)` / bubble arm
while solidity-lean matches `catch Error(string)` and binds a decoded reason — a **wrong
catch branch + wrong bound value**.

- **CB1 (NEW, SOUNDNESS wrong-branch + wrong-value, DIFFERENTIALLY-LIVE,
  CONFIRMED)** — see below. Forge (solc 0.8.35): a 36-byte revert `Error-selector ‖
  32 zero bytes` routes to `catch (bytes)` (branch 2); solidity-lean's `TryCatchClause`
  matches the Error clause (branch 1, reason `""`). Reachability is real but narrow
  (needs an adversarially/hand-framed callee returndata; canonical `Error`/`Panic`
  agree exactly), so it ranks below V1/DL1/M1 on likelihood while sharing their
  root cause (re-derivation of a returndata decode).

Everything else read this round is **faithful**: the low-level `(ok, ret)` pair is
responder-answered verbatim (no re-derivation); high-level bubbling forwards the
raw returndata byte-for-byte (empty→empty) exactly like `forwardingRevert`; the
`Panic(uint)` clause gate matches solc's `> 0x23` minimum exactly and tolerates
trailing bytes identically; the low-level `catch (bytes)` / empty-`catch` fallback
binds the full returndata like `extractReturndata`; `delegatecall` writes the
caller's storage (recipient=self → `adoptWorld` reads self storage back); and the
high-level-call `extcodesize` guard is modeled.

| # | Target | Verdict | Severity | Reachability |
|---|--------|---------|----------|--------------|
| **CB1** | `try/catch` `Error(string)` clause dispatch | **strict codec ≠ solc's `>=0x44` Error gate → wrong branch on short Error payload** | **SOUNDNESS (wrong branch + wrong value)** | **DIFFERENTIALLY-LIVE** (adversarial returndata; canonical agrees) |
| F1 | low-level `(bool ok, bytes ret)` | faithful (responder-answered verbatim) | — | n/a |
| F2 | high-level revert bubbling (raw forward) | faithful (matches `forwardingRevert`) | — | n/a |
| F3 | `catch Panic(uint)` clause dispatch | faithful (`>=0x24` gate, trailing tolerated) | — | n/a |
| F4 | low-level `catch (bytes)` / empty `catch` | faithful (binds full returndata) | — | n/a |
| F5 | `delegatecall` storage-write observability | faithful (recipient=self, adopted) | — | n/a |
| F6 | high-level `extcodesize` missing-code guard | faithful | — | n/a |
| F7 | success-path returndata decode-failure → empty revert | faithful (matches `abi_decode` revert(0,0)) | — | n/a |

**NEW findings this round: 1 differentially-live (SOUNDNESS wrong-branch +
wrong-value, CONFIRMED), 0 importer-masked.**

---

## CB1 — `try/catch` `Error(string)` clause matches on a short payload solc rejects (strict codec ≠ solc's `>= 0x44` Error gate) — SOUNDNESS

### The two algorithms

**solc.** `handleCatch` (`IRGeneratorForStatements.cpp:3460-3521`) dispatches the
Error/Panic clauses through a `switch returnDataSelector()`
(`YulUtilFunctions.cpp:4656-4674`: 0 on `returndatasize() < 4`, else the first
4 bytes). The `case Error(string)` arm calls **`tryDecodeErrorMessage`**
(`YulUtilFunctions.cpp:4676-4713`), a purpose-built *lenient* decoder that begins
with a **hard size gate**:

```yul
function try_decode_error_message() -> ret {
    if lt(returndatasize(), 0x44) { leave }          // <-- 68-byte hard gate
    ... // read offset at [4:36), bounds-check, read length, bounds-check string
    ret := msg                                        // nonzero ⇒ clause matches
}
```

Only if `tryDecodeErrorMessage` returns a nonzero pointer does solc set
`runFallback := 0` and run the Error clause (`:3477-3478`). Otherwise `runFallback`
stays `1` and control falls to the fallback clause (`catch (bytes)` / `catch {}`)
or, absent one, `forwardingRevert` (`:3514-3518`).

**solidity-lean.** `TryCatchClause.match?` for the Error clause
(`Interpreter.lean:7289-7296`) re-derives the match with the **strict standard
codec**:

```lean
| TryCatchClause.clause (some "Error") params body => do
    let selector ← revertBytesSelector? raw          -- needs >= 4 bytes
    if wordEq selector externalErrorSelector then
      let values ← abiDecodeValues? [Ty.bytesCalldata] (raw.drop selectorBytes)
      let frame ← BindingDecl.bindArgs? params values
      some (frame, body)
    else none
```

`abiDecodeValues? [Ty.bytesCalldata]` (`Interpreter.lean:4791-4795`, `4864-4866`)
reads the offset word (`readWord?`, needs 32 bytes), the length word at that
offset, and `length` string bytes — succeeding whenever those three reads are in
bounds, with **no `>= 0x44` floor**. For a *canonical* Error (offset `0x20`) the
length word forces `raw.length >= 68`, matching solc. But for a **degenerate
offset the length word overlaps an earlier region**, so the codec succeeds on a
much shorter buffer than solc's gate admits.

### Divergence (Forge-confirmed against solc 0.8.35)

Callee reverts with exactly `Error-selector ‖ 32 zero bytes` (36 bytes; the offset
word is `0`):

```solidity
assembly {
  let p := mload(0x40)
  mstore(p, 0x08c379a0...00)     // Error(string) selector
  mstore(add(p,4), 0)            // 32 zero bytes: offset == 0
  revert(p, 36)                  // returndatasize() == 36 < 0x44
}
```

Caller: `try c.short() {…} catch Error(string memory r) {branch 1} catch Panic(uint){branch 3} catch (bytes memory){branch 2}`.

- **solc** (Forge): `returndatasize() = 36 < 0x44` ⇒ `tryDecodeErrorMessage` leaves
  ⇒ `runFallback = 1` ⇒ **branch 2** (`catch (bytes)`), `r` never bound.
- **solidity-lean** (code trace): `revertBytesSelector? raw = Error selector` ✓;
  `abiDecodeValues? [bytesCalldata] (raw.drop 4)` on the 32-byte data reads
  `offset = readWord data 0 = 0`, `length = readWord data 0 = 0`,
  `bytes = readBytes data 32 0 = []` ⇒ decodes `Value.bytes []` ⇒ **branch 1**
  (`catch Error`), `r = ""`.

Forge ground truth (pinned solc 0.8.35), same harness:

| callee returndata | solc branch | solidity-lean branch |
|---|---|---|
| `Error-selector ‖ 32×0x00` (36 B, offset 0) | **2** (`catch bytes`) | **1** (`catch Error`, `r=""`) |
| canonical `Error("")` (68 B, offset `0x20`) | 1 (`catch Error`, `r=""`) | 1 (`catch Error`, `r=""`) — MATCH |
| `Panic-selector ‖ 0x11 ‖ 8 trailing` (44 B) | 3 (`catch Panic`, code 17) | 3 (`catch Panic`, code 17) — MATCH |

So the divergence is isolated to the **Error** clause and to returndata whose size
is in `[36, 67]` with an offset word small enough that the length read stays in
bounds (the offset-`0` case is the minimal repro). Both sides agree exactly on
canonical Error, on all Panic shapes (solc's `> 0x23` gate == solidity-lean's structural
36-byte minimum), and on custom-error / empty returndata (both fall to the bytes
clause).

### Root cause & why it is the V1 class

solc uses **two different decoders**: the strict standard `abi_decode` for return
*values*, and hand-written *lenient* decoders (`tryDecodeErrorMessage` /
`tryDecodePanicData`) with bespoke size gates for `catch Error`/`catch Panic`.
solidity-lean collapses both onto its single strict codec (`abiDecodeValues?`). The
strict codec happens to coincide with `tryDecodePanicData` (both bottom out at 36
bytes) but **not** with `tryDecodeErrorMessage`, whose `>= 0x44` floor is stricter
than the codec's structural minimum for a degenerate offset. This is exactly the
V1 pattern — a *returndata decode re-derivation* that silently differs from solc's
concrete hand-written routine on a corpus-missed input.

### Reachability & classification

**DIFFERENTIALLY-LIVE.** The caller is ordinary solc-compiled `try/catch`; the
callee's returndata is responder-supplied, so a fixture that returns the 36-byte
`Error`-framed payload drives the divergence. **Untested in the corpus** (no
hand-framed short-Error revert present), so unflagged by the differential harness.
Likelihood is lower than V1/DL1/M1 because it needs a non-canonical callee
returndata — a well-behaved contract's `revert("…")` always emits the canonical
`>= 0x44` form on which both sides agree. **Severity: SOUNDNESS (wrong catch branch
+ wrong bound value).** **Confidence: CONFIRMED** (solc source + Forge ground
truth + solidity-lean code trace).

### Suggested fix (for a fix-agent — not applied here)

Gate the Error clause on `raw.length >= 0x44` (and, symmetrically, keep the Panic
clause's implicit `>= 0x24`) before invoking the codec — i.e. mirror
`tryDecodeErrorMessage`'s hard floor in `TryCatchClause.match?` rather than relying
on the strict codec's structural minimum. The canonical path is unchanged; only
the short-payload edge moves to the fallback clause, matching solc.

---

## Faithful surfaces (earned negatives this round)

- **F1 — low-level `(bool ok, bytes ret)`.** `decodeCallResponse`
  (`Interpreter.lean:2277-2282`) copies `response.success` and
  `byteArrayToBytes response.returnData` verbatim; the call site
  (`:6403-6430`) returns `(boolWord result.success, Value.bytes result.output)`.
  No re-derivation — the success flag and returndata are exactly what the responder
  (the callee's real execution, in a fixture) answers, mirroring EVM
  `CALL`+`returndatacopy`. All three kinds share this path;
  `buildCallRequest` (`:2231-2272`) sets the kind-correct frame
  (delegatecall recipient=self / no transfer; staticcall no transfer).
- **F2 — high-level revert bubbling.** On a failed high-level call with no
  matching catch clause, solidity-lean reverts with `RevertData.fromRawBytes output`
  (`:8397-8401`); `fromRawBytes` (`:305-309`) yields `empty` iff the output is
  empty, else `raw output`. solc's `forwardingRevert`
  (`YulUtilFunctions.cpp:4147-4172`) does `returndatacopy(pos,0,returndatasize());
  revert(pos, returndatasize())` — the raw bytes verbatim, empty→`revert(0,0)`.
  Byte-for-byte match, including `Error`/`Panic`/custom/empty shapes.
- **F3 — `catch Panic(uint)`.** `TryCatchClause.match?` Panic arm
  (`:7297-7304`) checks the Panic selector then `abiDecodeValues? [uint256]
  (raw.drop 4)` — needs `raw.length >= 36` and reads one word, ignoring trailing
  bytes. solc's `tryDecodePanicData` (`YulUtilFunctions.cpp:4715-4733`) gates on
  `gt(returndatasize(), 0x23)` (== 36) and reads the word at offset 4, also
  ignoring trailing bytes. Structurally identical; Forge confirms a 44-byte
  Panic-with-trailing decodes to code 17 on both.
- **F4 — low-level `catch (bytes)` / `catch {}`.** `matchLowLevel?`
  (`:7280-7285`) binds `[]` for a param-less clause or `[Value.bytes raw]` for the
  single-`bytes` clause — the full returndata. solc's `extractReturndata`
  (`YulUtilFunctions.cpp:4735-4762`) copies the whole returndata (empty→empty
  array). The unnamed catch is grammar-forced last, so solidity-lean's source-order
  `findMatch?` never shadows an Error/Panic clause with it.
- **F5 — `delegatecall` storage-write observability.** `buildCallRequest`
  sets `recipient := wordToAddress context.self` and `transferValue := 0` for
  delegatecall (`:2243-2252`); on resume `adoptWorld` (`:2139-2153`) reads the
  self account's storage/transient/balance/nonce back out of
  `postWorld.accounts[self]`. So a delegate that (in the responder's world) writes
  the caller's storage has those writes adopted into `State.storage` — the correct
  EVM semantics (callee code, caller's storage). No independent re-derivation;
  responder-answered like `call`.
- **F6 — high-level `extcodesize` guard.** `missingCode := checkTargetCode &&
  !(envAccountHasCode …)` short-circuits to `LowLevelCallResult.failedRequest`
  (`:8335-8344`) — a typed external call to a codeless address fails without
  emitting a query, matching solc's `extcodesize` check on `ContractType` calls.
  Low-level `.call` carries no such guard (calling an EOA succeeds), matching solc.
- **F7 — success-path returndata decode failure.** On a *successful* high-level
  call whose returndata cannot be decoded or fails return-value cleanup, solidity-lean
  reverts `RevertData.empty` (`:8377-8386`), matching solc's `abi_decode`
  validation failure `revert(0, 0)`.

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] Low-level `call`/`staticcall`/`delegatecall` `(ok, ret)` return — **FAITHFUL**
  (F1, responder-answered)
- [x] High-level call revert bubbling (raw forward, empty→empty) — **FAITHFUL** (F2)
- [x] `try/catch Error(string)` clause dispatch — **WRONG on short payload**
  (CB1, NEW, CONFIRMED)
- [x] `try/catch Panic(uint)` clause dispatch — **FAITHFUL** (F3)
- [x] `try/catch (bytes)` / empty `catch` fallback — **FAITHFUL** (F4)
- [x] `delegatecall` storage-write observability — **FAITHFUL** (F5)
- [x] high-level `extcodesize` missing-code guard — **FAITHFUL** (F6)
- [x] success-path returndata decode/cleanup failure → empty revert — **FAITHFUL**
  (F7)

**Still NOT reached (worklist for later rounds):**

- Transient-storage (`tstore`/`tload`) slot-allocation ORDER across a diamond —
  shares DL1's traversal; **gated on the DL1 fix landing** (Round-10).
- `create`/`create2`/`selfdestruct` execution observables (deployed address,
  balance movement, constructor-revert bubbling) + precompile 0x05–0x0a input
  framing (Round-11).
- ABI encoder deep edges, `encodeCall`/`encodeWithSignature` dynamic edges,
  `blockhash`/`blobhash` window acceptance, event/error deep encoding corners
  (Round-12).
- M1-family completion (memory-ref alias across the call boundary, tuple
  destructure) — **gated on the M1 fix landing** (Memory-round-3).

---

## Bottom line

Round 9 targeted the open-world call-return & revert-bubbling surface — the
plan's top UNEXPLORED P0 — and found **CB1**: solidity-lean re-derives the `try/catch`
`Error(string)` clause match with its strict standard ABI codec, whose structural
minimum (36 bytes for a degenerate offset) is looser than solc's hard
`returndatasize() >= 0x44` gate in the purpose-built `tryDecodeErrorMessage`. A
callee that reverts with a short, non-canonically-framed `Error`-selector payload
(minimally `Error-selector ‖ 32 zero bytes`, 36 bytes) is routed to
`catch (bytes)` by solc but to `catch Error(string)` (reason `""`) by solidity-lean — a
wrong catch branch and a wrong bound value, Forge-confirmed against the pinned
solc. Every other surface read is faithful: the low-level `(ok, ret)` pair is
answered verbatim, high-level bubbling forwards the raw returndata byte-for-byte,
the `Panic` clause gate matches exactly, `delegatecall` writes the caller's storage
via the recipient=self + `adoptWorld` path, and the `extcodesize` guard is modeled.
CB1 shares V1/DL1/M1's root cause (a returndata-decode re-derivation) but is
narrower in reach — canonical `Error`/`Panic`/custom/empty reverts all agree.

**NEW divergences this round: 1 differentially-live (SOUNDNESS wrong-branch +
wrong-value, CONFIRMED), 0 importer-masked.**
</content>
</invoke>
