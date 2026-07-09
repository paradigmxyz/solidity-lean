# solc vs solidity-lean: address-type members & low-level calls review

Scope: observable semantics of `<address>.balance`/`.code`/`.codehash`, low-level
`.call`/`.staticcall`/`.delegatecall`, `.send`/`.transfer`, `payable(...)` /
`address(this)`, and the non-payable-address over-accept edge. Reviewed against
solc v0.8.35 (pin 47b9dedd, binary `/Users/dan/.solc-select/artifacts/solc-0.8.35`)
and the LEGACY differential corpus. Bytecode content, gas metering/stipend, and
the closed-world multi-contract model are out of scope by charter.

Reviewer stance: REVIEW ONLY — no Lean/fixture edits.

## Verdict: clean negative

No new divergence found. Every observable in scope either matches solc exactly or
is governed by an already-documented intentional exclusion. Details and evidence
below, with the intentional-exclusion boundaries called out explicitly.

---

## Confirmed matches (with evidence)

### 1. `.send` / `.transfer` require `address payable` (over-accept: none)
solc rejects `.send`/`.transfer` on a plain `address`:

```
Error: "send" and "transfer" are only available for objects of type
"address payable", not "address".
```
(verified: `address(this).transfer(1)` on the pinned binary.)

solidity-lean requires `isPayableAddress` for both members in the type checker —
`TypeCheck.lean:6218-6231` (call form) and `6760-6784` (options form), with
`Ty.isPayableAddress` matching only `Ty.address true` (`TypeCheck.lean:4155-4157`).
`address(this)` lowers to `Ty.address false` (`TypeCheck.lean` address-of-this and
`Interface.lean` payable-conversion → `Ty.address true` only under `payable(...)`).
Match. Classification: correct reject. Confidence: high.

### 2. `.call` / `.staticcall` / `.delegatecall` allowed on non-payable address
solc compiles `a.call("")`, `a.staticcall(...)`, `a.delegatecall(...)` on plain
`address` (verified: T2.sol compiled). solidity-lean gates these on
`isAddressBuiltinReceiver` (matches both `Ty.address true/false`) —
`TypeCheck.lean:6731-6759`. Match. Confidence: high.

### 3. (bool, bytes) return shape of low-level calls
solidity-lean returns `Value.tuple [bool success, bytes output]` directly from the
oracle-answered call result — `Interpreter.lean:6579-6582`. Return type is
`lowLevelCallReturnTy = (bool, bytes)` (`Interface.lean:3794`, `TypeCheck.lean:4181`).
Match with solc's `(bool, bytes memory)`. Confidence: high.

### 4. NO extcodesize existence guard on low-level calls / send / transfer
This is the key charter item. solc emits a raw `CALL` (`5af1`) for `a.call("")`
with no `extcodesize` guard (confirmed in T2.sol bytecode: the guard opcode
sequence is absent; `EXTCODECOPY`/`933c` appears only for the separate `.code`
read). The high-level typed-call guard (A1/A3) does NOT apply here.

solidity-lean: the low-level path (`Interpreter.lean:6526-6585`) calls
`emitLowLevelCall` and returns `result.success`/`result.output` with no code check.
`transfer` desugars to `Stmt.tryExternalCall ... checkTargetCode=false`
(`Interface.lean:5661-5667`); `send` desugars to a bare `lowLevelCall` indexed `[0]`
(`Interface.lean:4380-4392`). Both carry `checkTargetCode=false`. So a low-level
call / send / transfer to a codeless address yields `success=true`, empty
returndata (and value moved for call/send/transfer) — matching solc — NOT a revert.
Match. Confidence: high. (Guard-present behavior for high-level typed calls is
unchanged and out of re-review scope.)

### 5. Call-option constraints (over-accept: none)
- `value` allowed on `.call`, rejected on `.staticcall`/`.delegatecall`:
  `TypeCheck.lean:6738-6743` (`requireCallOptionsAllowedNames ["gas","value"]` vs
  `["gas"]`). Matches solc; corpus `low-level-call-options/invalid/ValueOnStaticcall.sol`
  and `ValueOnDelegatecall.sol` already lock this.
- Named arguments on low-level calls rejected (`TypeCheck.lean:6733`); corpus
  `NamedLowLevelArguments.sol`.
- `salt` on low-level call rejected; corpus `SaltOnLowLevelCall.sol`.
- `.send`/`.transfer` take no call options (`requireCallOptionsAllowedNames []`,
  `TypeCheck.lean:6742-6743`). Match.

### 6. `.balance` / `.code` / `.codehash` member availability
- All three require an address-typed receiver via `isAddressBuiltinReceiver`
  (`TypeCheck.lean:5565-5595`); a contract- or library-typed receiver is rejected.
  This matches solc (you must write `address(c).balance`, etc.) and is locked by
  corpus `address-member-receivers/invalid/{Contract,Library}{Balance,Code,Codehash}.sol`.
- `.code` types as `bytes`, `.codehash` as `bytes32` (gated on Constantinople+,
  trivially satisfied at 0.8.35), `.balance` as `uint256`. Match.

### 7. EIP-1052 codehash structure
`State.envAccountCodehash` (`Interpreter.lean:2230-2239`): post-adoption a
nonexistent account → `0`; an existing account → `keccakWord(codeBytes)`, so an
existing empty-code account yields `keccak256("")`. This is the correct EIP-1052
split (0 for nonexistent, `keccak256("")` for empty-but-existing). Pre-adoption the
oracle seed map (`context.accountCodehashes`) is authoritative. Match on structure.

### 8. Reads routed through the open world
`.balance`/`.code`/`.codehash` resolve through
`envAccountBalance`/`envAccountCode`/`envAccountCodehash`
(`Interpreter.lean:2195-2239`), which read the adopted post-world when present else
the oracle seed maps — never bypassing the differential answer. `address(this).balance`
threads through the A2 intra-frame `selfBalance` accounting (`Interpreter.lean:864-872`).
Balance flows only through adoption. No independent, divergent computation.

---

## Intentional-exclusion boundaries (NOT bugs)

- **`.code` bytecode CONTENT**: `.code` returns the bytes carried by the adopted
  account / oracle seed map (`Interpreter.lean:2206-2214`). Deployed-bytecode
  content is an explicit charter exclusion. `.code.length` is structurally
  supported (`.code` → `bytes`, then `.length`), but its concrete value is only as
  faithful as the harness-supplied code bytes — this is the exclusion boundary, not
  a semantic gap.
- **Post-adoption codehash of a code-bearing account**: `envAccountCodehash`
  recomputes `keccakWord(codeBytes)` post-adoption. If the adopted world strips a
  contract's runtime code (bytecode-content exclusion), this yields `keccak256("")`
  rather than the real code hash. The code explicitly documents (`Interpreter.lean:2226-2229`)
  that the seed map carries the authoritative oracle codehash pre-adoption. This is
  a fidelity consequence of the bytecode-content exclusion, not an interpreter bug —
  flagged for awareness only.
- **2300 gas stipend** on `send`/`transfer` (`Interface.lean:4390`, `5666`): the
  literal `2300` is carried for request fidelity, but gas metering is out of scope;
  the observable success/failure and balance effect come from the oracle answer.

---

## Notes on rejections that coincide with solc

- `a.call()` (no bytes argument): solc errors ("requires a single bytes
  argument"); solidity-lean has no lowering pattern for the zero-arg form, so it
  rejects via lowering failure. Same accept/reject outcome (different diagnostic
  channel, not observable). Not a divergence.

## Method / confidence
Type-accept/reject items were checked directly on the pinned solc binary
(T1/T2/T3). Runtime observables (bool/bytes/balance) are answered by the
differential oracle and reproduced verbatim by the interpreter, so faithfulness is
structural rather than a place solidity-lean could independently diverge — the only
independent computation in scope is post-adoption codehash, addressed above.
Overall confidence: high that no new in-scope divergence exists.
