# solc 0.8.35 vs solidity-lean: try/catch statement semantics review

Search-only divergence hunt over try/catch **clause routing / decoding** semantics.
Ground truth: pinned solc 0.8.35 legacy codegen (optimizer=false, no via-IR, ABI
coder v2). solc source at `/Users/dan/Projects/solidity-src`.

## Verdict: CLEAN NEGATIVE (no divergence found)

solidity-lean's try/catch dispatch is a faithful mirror of solc 0.8.35's legacy
codegen across all six focus areas. Confidence 90%. Verified by reading BOTH
sides' source end-to-end AND by three empirical Forge probes against the pinned
solc/EVM (all pass).

## What solc does (legacy codegen, definitive trace)

- **Success/failure split** — `ContractCompiler::visit(TryStatement)`
  (ContractCompiler.cpp:970) + `appendExternalFunctionCall(..., _tryCall=true)`
  (ExpressionCompiler.cpp:2954): after the CALL, `DUP1 ISZERO` jumps to `endTag`
  on **failure** (leaving success flag=0 for catch routing). On **success** the
  flag is popped and the return tuple is decoded via `utils().abiDecode(...)`
  (ExpressionCompiler.cpp:3020) — a decode failure there `revert`s and is
  **uncatchable** (it is past the catch branch point).
- **Catch dispatch** — `ContractCompiler::handleCatch` (ContractCompiler.cpp:1015):
  computes the 4-byte selector via `return_data_selector` (0 if returndatasize<4),
  then routes **by kind, order-independently**:
  - `Error` clause: if selector==`0x08c379a0` AND `tryDecodeErrorMessage` succeeds
    → Error clause; else fall to fallback.
  - `Panic` clause: if selector==`0x4e487b71` AND `tryDecodePanicData` succeeds
    → Panic clause; else fall to fallback.
  - fallback (`catch (bytes)`/`catch{}`): binds full returndata as bytes; if
    absent, **re-reverts** `revert(0, returndatasize())` (bubbles exact bytes).
- **Decode gates** (YulUtilFunctions.cpp): `tryDecodeErrorMessage` requires
  `returndatasize >= 0x44` (68) plus offset/length in-bounds; `tryDecodePanicData`
  requires `returndatasize > 0x23` (>= 36) and reads the code word directly (no
  offset indirection, no further validation). `return_data_selector` yields 0 for
  returndata < 4 bytes.
- **TypeChecker** (TypeChecker.cpp:1029): Error→`string memory`, Panic→`uint256`,
  unnamed→`bytes memory` or empty; duplicates rejected; **clause order is NOT
  constrained** (Error/Panic/low-level may appear in any order).

## What solidity-lean does (matching, file:line)

- Classification: `revertClassify` (Interpreter.lean:7564) — Error requires
  selector match AND `raw.length ≥ 68` AND `abiDecodeValues? [bytesCalldata]`
  succeeds; Panic requires selector match AND `raw.length ≥ 36` AND
  `abiDecodeValues? [uint256]` succeeds; else `lowLevel`. `revertBytesSelector?`
  (7537) yields `none` for <4 bytes → `lowLevel`. Bounds are **identical** to
  solc's Yul gates (the bytesCalldata `readWord?/readBytes?` bounds reduce exactly
  to solc's `offset+0x24<=rds` / `end<=rds-4`; uint256 read needs `>=32` post-
  selector bytes == solc's `>0x23`; trailing data tolerated on both sides).
- Kind-based routing: `TryCatchClause.findMatch?` (7606) — runs the typed clause
  for the classified kind if present (`errorClause?`/`panicClause?`), else falls
  through to `catchAllClause?`; `none` (no matching clause) propagates the revert.
  Order-independent, matching handleCatch.
- Success path: `Stmt.tryExternalCall` handler (Interpreter.lean:8699-8729) —
  `abiDecodeValues?` + `AbiCleanups.acceptOrUnspecified`; on decode/cleanup
  failure returns `Result.reverted ... RevertData.empty` **out of** the try
  (uncatchable), exactly solc's uncatchable empty `revert(0,0)`.
- Catch path: 8730-8744 — `findMatch?`; on `none`, re-reverts
  `RevertData.fromRawBytes output` (7605 / 305) preserving exact bytes, == solc's
  `revert(0, returndatasize())` bubble.
- `new C(...)` try/catch: `Stmt.tryContractCreate` handler (8752-8855) — same
  routing; success binds the created address; no return-tuple decode path
  (correct — create returns an address, not an ABI tuple).
- TypeCheck: `checkCatchClauseHeader` (TypeCheck.lean:9167) + duplicate-kind check
  `checkCatchClauseKindsUnique` (9226) — mirrors solc's type rules incl.
  order-independence. `Parameter.isPanicCode` (9142) enforces `uint256`, no
  data location.

## Per focus-area findings

1. **Clause routing** — match. By-kind, order-independent; unmatched typed data
   falls to low-level; no low-level → bubble.
2. **Panic(uint) binding** — fully supported (parse → `panicClause?` → decode
   `uint256`). Probe: division-by-zero routed to `catch Panic(uint p)` with
   `p == 0x12`.
3. **try-with-returns decode failure** — match. Callee SUCCEEDS but returndata
   (8 bytes) fails to decode as `uint256` → **uncatchable empty revert** (NOT
   routed to `catch (bytes)`). Empirically confirmed (ok=false, data.length==0).
4. **Success-path returndata decode** — match. Uses full returndata + coder-v2
   validation + cleanups; failures revert empty uncatchably.
5. **new-contract try/catch** — match (created-address bind; same catch routing).
6. **Empty returndata routing** — match. Bare `revert()` → `lowLevel` → only
   `catch (bytes)`/`catch{}` (NOT `catch Error`); with no low-level clause it
   bubbles. Empirically confirmed.

## Empirical probes (pinned solc 0.8.35 + Forge, all PASS)

Scratchpad project `.../scratchpad/tc`:
- `test_decode_fail_uncatchable`: success + undecodable returndata → outer call
  reverts with empty data (uncaught).
- `test_routing`: Error→Error clause; Panic→Panic clause (code 0x12); bare
  `revert()`→low-level clause; bare `revert()` with only Error+Panic clauses →
  bubbles uncaught; Panic caught by Panic clause when no low-level present.

## Residual uncertainty (why 90%, not 100%)

Not exhaustively probed: non-canonical Error-string offsets, hand-crafted
malformed Error/Panic payloads with unusual in-bounds offsets, and enum/bool
cleanup failures on the success return tuple. Source-level analysis shows the
bounds reduce to identical predicates, but these were not each independently
run against the EVM. No divergence is expected on any of them.
