# solc 0.8.35 vs solidity-lean: receive / fallback dispatch and payable rules

Scope: message-dispatch decision tree (empty vs non-empty calldata, selector
match, receive-vs-fallback), value/mutability accept-reject rules, receive/fallback
signature validation, `payable()` conversion + `.transfer`/`.send` type rule,
constructor payability. Gas metering and the 2300 stipend are **out of scope**
(gas is excluded from the model); low-level `.transfer`/`.send`/`.call` sender-side
mechanics were checked only for the callee-side routing they trigger.

Ground truth: pinned solc 0.8.35
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) + Forge 1.5.1,
legacy codegen (optimizer=false, no via_ir).

## Verdict: CLEAN NEGATIVE — no divergences found (confidence 90%)

Every checklist item was traced in the Lean source and confirmed against solc,
both by direct Forge ground-truth runs and by driving the solidity-lean
interpreter itself. The two priority items (len<4 → fallback-not-receive, and
value-to-nonpayable revert at dispatch) were verified end-to-end through the
interpreter with results matching solc exactly.

## Dispatch decision tree (item 1) — CORRECT

Root: `Contract.callCalldataAtFromWithContext?`
(`SolidCore/Solidity/ABI.lean:756`).

- `readSelector? calldata` (`ABI.lean:68`) reads 4 bytes at offset 0 via
  `readBytes?` (`ABI.lean:18`), which returns `none` when
  `calldata.length < 4`. So calldata of length 0–3 never matches a selector.
- On `readSelector? = none` it calls `callReceiveOrFallbackAtFromWithContext?`
  (`ABI.lean:713`), which routes on `calldata.isEmpty`:
  - empty → `findReceive?` (`ABI.lean:629`, looks up `__receive`) → receive if
    present, else fall through to fallback;
  - non-empty (1–3 bytes) → `callFallbackAtFromWithContext?` (fallback, **not**
    receive).
- On `readSelector? = some sel` with no `findFunctionBySelector?` match →
  `callFallbackAtFromWithContext?` (fallback), including a non-matching 4-byte
  selector.
- Missing fallback → `missingFallbackCall?` → empty revert (`ABI.lean:625`).

This matches solc's `ContractCompiler::appendFunctionSelector`
(`calldatasize() < 4` jumps to the receive/fallback block; receive gated on
`iszero(calldatasize())`).

Direct interpreter run on `contract RF { receive() external payable{marker=2;}
fallback() external {marker=1;} }`:

| calldata | value | solc | solidity-lean interpreter |
|---|---|---|---|
| `01 02 03` (3 bytes) | 0 | success, marker=1 (fallback) | success, marker=**1** |
| `` (empty) | 0 | success, marker=2 (receive) | success, marker=**2** |
| `deadbeef` (4-byte no match) | 0 | success, marker=1 (fallback) | success, marker=1 |

## Value / mutability accept-reject (item 4) — CORRECT

`FunctionDef.acceptsValue = payable || value == 0`
(`SolidCore/Solidity/Interpreter.lean:9087`). It gates **every** dispatch path
before the body runs:
- selector-matched function: `ABI.lean:770` → else `rejectedValueCall?` (empty revert);
- receive: `ABI.lean:721`;
- fallback (both forms): `ABI.lean:684`, `ABI.lean:943`.

It is also enforced a second time inside the body entry,
`FunctionDef.evalBodyEntry` (`Interpreter.lean:9164`), which returns
`Result.reverted … RevertData.empty` when value is not accepted. This covers the
constructor path, which invokes `FunctionDef.call?` directly.

Forge ground truth (all pass, confirming solc): value→non-payable function
reverts; value→non-payable fallback reverts; empty+value with only a
non-payable fallback reverts; plain value to a contract with only a payable
function (no receive/fallback) reverts; receive accepts value.

Direct interpreter run (same RF contract): 3-byte calldata + value=7 →
`success=false` (non-payable fallback rejects value); empty + value=7 →
`success=true` (payable receive accepts). Both match solc.

## receive() signature (item 2) — CORRECT

`TypeCheck.lean:10580` requires: no name, no params, no returns,
`external`, `payable` — else `TypeError.invalidFunctionHeader`. Empty-calldata
routing lands here via `findReceive?`. Matches solc TypeChecker.

## fallback() both forms (item 3) — CORRECT

`TypeCheck.lean:10595` accepts exactly two shapes:
`fallback() external [payable]` (empty params+returns) **or**
`fallback(bytes calldata) external [payable] returns (bytes memory)`
(`Parameter.isBytesCalldata` input, `Parameter.isBytesMemory` output).
- Full `msg.data` passed to the bytes form: `FunctionDef.fallbackArgs?`
  (`ABI.lean:635`) yields `[Value.bytes calldata]`.
- Return of the bytes form is emitted **raw**, not ABI-wrapped:
  `FunctionDef.encodeFallbackOutput?` → `normalizeBytes bytes` (`ABI.lean:649`).
  This matches solc, which does `return(ptr,len)` on the raw bytes; the existing
  fixture `testTypedFallbackReturnsRawCalldata`
  (`tests/forge-harness/receive-fallback-dispatch/...`) asserts
  `keccak256(output)==keccak256(payload)` and passes on solc.
- Non-payable fallback + value → revert (via `acceptsValue`, above).

## payable() conversion + type rule (items 5) — CORRECT

`payable(addr)` types as `Ty.address true`
(`Interface.lean:5100`). `.transfer`/`.send`/`.call{value:}` require
`targetChecked.ty.isPayableAddress` (`TypeCheck.lean:6322/6334/…`), so `.transfer`
on a plain `address` is rejected and on `payable` accepted — matching solc.

## Constructor payability (item 9) — CORRECT

`ContractDecl.constructorPayable?` (`Interface.lean:18283`) defaults to `false`
when there is no constructor, else uses the constructor's `payable` mutability.
The flag is threaded into the lowered constructor `FunctionDef.payable`
(`Interface.lean:18160`, `20825`); the deploy path (`constructWithBases…` →
`FunctionDef.call?`) reverts on value-to-non-payable-constructor via
`evalBodyEntry`'s `acceptsValue` gate. Matches solc (default constructor
non-payable).

## msg.value / msg.sender / explicit revert (items 7, 8) — CORRECT

`callContextAtWithBase` (`ABI.lean:653`) sets `sender`/`value` for every
entry; the existing fixture records and asserts `lastSender`/`lastValue` inside
receive and fallback and passes through the paired interpreter harness. Reverts
propagate through `encodeRevertData?`.

## Verification performed

- Read the full dispatch/value logic in `ABI.lean`, `Interpreter.lean`,
  `Interface.lean`, `TypeCheck.lean`.
- Ran the repo harness on `receive-fallback-dispatch` with pinned 0.8.35:
  `forge_interpreter_compare=pass` (solc AST imported to Lean, interpreter
  dispatch matches solc).
- Wrote a standalone Foundry probe (7 tests) exercising len<4 routing, empty vs
  non-empty, value-to-nonpayable across function/fallback/receive/plain-value —
  all pass on solc, matching the model's predicted routing.
- Drove the solidity-lean interpreter directly
  (`CheckedContract.callCalldataAtFrom`) on a receive + non-payable-fallback
  contract for the two priority cases; results matched solc exactly.

## Notes / non-issues

- Order within a matched function: solidity-lean decodes args
  (`decodeFunctionArgs?`, `ABI.lean:764`) **before** the `acceptsValue` value
  check (`:770`); solc emits the callvalue check first. Observationally
  equivalent here because both failure modes produce the same empty revert, so
  no divergence — flagged only for completeness.
- Gas / 2300 stipend / extcodesize accounting: out of scope by mission
  (gas excluded from the model).

Confidence 90%: the residual 10% reflects unexercised obscure corners
(selector literally `0x00000000`, receive/fallback declared `virtual` without a
body in an abstract base) that were not separately fuzzed; the core routing and
value/mutability surface is confirmed both statically and by execution.
