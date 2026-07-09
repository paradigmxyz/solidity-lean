# solidity-lean semantics divergences — handoff to the semantics agent

Candidate and confirmed solidity-lean-vs-solc/EVM divergences surfaced by two review
agents (2026-07-08). All line numbers are in `SolidCore/Solidity/` unless noted.
None are acted on here — this is a to-investigate list for the semantics work.

**Cross-check first:** docs rounds 8–12 (`solc-implementation-divergences-{8,9,10}.md`
etc.) and the memory/DL1 fixes (commits `ce58cfd`, `4d2a5c0`, `3043a9b`, `fae2575`)
landed concurrently — verify each item below is still open against the latest
docs before deep-diving, and fingerprint every confirmed one into
`contest/known_gaps.py` so contest submissions dedup.

---

## A. CONFIRMED soundness divergences (external-call existence & try/catch)

These are verified against solc 0.8.35 (two with IR probes). They are runtime
wrong-control-flow divergences on solc-accepted programs, and none is masked by
the importer.

### A1 — `try` + void external call to a **codeless** address: solidity-lean runs `catch`; solc reverts the caller uncatchably
- **solc:** the extcodesize guard is emitted for any high-level call with return
  head size 0, with **no exception for `tryCall`** (`IRGeneratorForStatements.cpp:2705-2707`
  emits `if iszero(extcodesize(addr)) { revertNoCode() }`; decision at `:2750-2762`).
  The guard is a plain `revert(0,0)` in the caller **before** the call, outside
  the `switch trySuccessCondition` — so `try` **cannot** catch the no-code case.
- **solidity-lean:** `Interface.lean:14256` lowers `try` with `checkTargetCode := returns.isEmpty`;
  the interpreter maps missing code to `LowLevelCallResult.failedRequest`
  (`Interpreter.lean:8335-8344`), which flows into the catch dispatch
  (`Interpreter.lean:8387-8401`) — the bare/low-level catch matches and its body runs.
- **Probe:** `interface I { function f() external; } contract C { function probe(address a) public returns (uint) { try I(a).f() { return 1; } catch { return 2; } } }`
  with `a` an EOA/codeless address: **solc reverts the whole call (empty data); solidity-lean returns `2`.**
- Corrects round-9 **F6** ("high-level extcodesize guard — faithful"), which only
  considered the plain-call observable.

### A2 — catch-clause dispatch is source-order first-match; solc dispatches by KIND
- **solc:** clause order is unconstrained (parser `Parser.cpp:1599-1603`;
  typechecker enforces only per-kind uniqueness); codegen fetches clauses **by
  kind** (`errorClause()/panicClause()/fallbackClause()`, `AST.cpp:1072-1082`).
- **solidity-lean:** `TryCatchClause.findMatch?` (`Interpreter.lean:7310-7316`) is
  first-match over the **source-ordered** clause list, and the low-level clause
  matches **any** payload (`matchLowLevel?`, `Interpreter.lean:7280-7285`). With
  `catch (bytes)` / bare `catch` listed **before** `catch Error` / `catch Panic`,
  solidity-lean runs the fallback where solc runs the kind clause.
- **Probe:** `try this.gv() {} catch (bytes memory) { return 1; } catch Error(string memory) { return 2; }`
  where `gv()` does `revert("boom")`: **solc returns `2`, solidity-lean returns `1`.**
  Same shadowing for `catch (bytes)` before `catch Panic(uint)`.
- Refutes round-9 **F4**'s "unnamed catch is grammar-forced last" justification —
  the parser imposes no such constraint.

### A3 — extcodesize check skipped for non-identifier receiver shapes (plain void call)
- **solc:** the `checkExtcodesize` template is receiver-shape-independent — any
  void high-level external call gets the guard (`IRGeneratorForStatements.cpp:2705, 2755-2761`).
- **solidity-lean:** the plain-statement lowering gates the check on receiver **shape**:
  `Expr.externalCallNeedsCodeCheckWithEnv` (`Interface.lean:5198-5206`) requires
  `Expr.externalCallTargetNeedsCodeCheckWithEnv` (`:5186-5196`), which is true
  only for an **identifier** of contract type (local/param/state var/`this`) or a
  **direct cast `C(x)`**. Receivers like `contracts[i].f()`, `s.field.f()`,
  `m[k].f()`, `factory.get().f()` fall to `_ => false` → no existence check.
  (Some legacy sites pass an empty env — `Interface.lean:6160-6165` — disabling
  the check for ident receivers too.)
- **Probe:** `interface I { function f() external; } contract C { I[] ts; function add(address a) public { ts.push(I(a)); } function probe() public returns (uint) { ts[0].f(); return 7; } }`
  with a codeless target: **solc reverts (guard); solidity-lean returns `7`.**
  (CONFIRMED in code; observable INFERRED.)

---

## B. CANDIDATE divergences (ranked; each needs a differential probe)

Highest-signal first. "Candidate" = concrete suspect code path + mechanism, not
yet run on solc.

### B1 — Storage packing of narrow value-type arrays that straddle slot boundaries (high)
`StorageLayout.slotSpan` (`Interpreter.lean:1355-1358`) computes a fixed array's
span as `natCeilDiv (size * widthBytes) 32`, and `arrayElementOffsetAndLayout?`
(`~1455-1466`) locates element `i` at `slot = i*widthBytes/32`,
`offset = i*widthBytes%32` — i.e. it bit-packs and lets an element **straddle two
slots**. solc never splits a value-type element across a slot: `uint72[7]`
occupies 3 slots in solc (3 elems/slot) but 2 here. Any `uintN/intN/bytesN` array
with `32 % (N/8) != 0` (uint72/uint96/uint200/bytes3/bytes5…) diverges in slot
count and per-element offset. Reachability depends on the importer emitting
`packedScalar` for such widths.

### B2 — Unchecked exponentiation uses an O(exponent) naive loop (high)
`checkedExpLoop` (`~5316`) and `checkedSignedExpLoop` (`~5399`) recurse
structurally `norm exponent` times (a `Nat` up to 2²⁵⁶−1). Inside `unchecked`,
`x ** y` with a large runtime `y` (e.g. `2 ** userValue`) makes solc return
`base^exp mod 2²⁵⁶` in O(log y) while solidity-lean attempts up to 2²⁵⁶ iterations —
a hang/timeout instead of the wrapped value. (Note: this compounds the contest
harness's fuel-timeout handling — now routed to NEEDS_REVIEW, not a false gap.)

### B3 — Narrow signed division/negation overflow only special-cases the 256-bit min (high)
`checkedSignedDiv` (`5376-5384`) guards only `isSignedMinWord = 2²⁵⁵` and
`isSignedNegOneWord`; likewise `checkedSignedNeg` (`~5364`). For `int8 a = -128; a / -1`
(or `-a`) the true overflow is at the int8 level. Correctness then rests entirely
on an enclosing `intCleanup`; if the importer omits a cleanup wrapper on a
division/negation result, solidity-lean returns `128` instead of reverting `Panic(0x11)`.

### B4 — Modifier placeholder substitution: verify nested / multi-`_` handling (medium)
Two lowerings exist: `Interface.lean:5884` (`replaceTopLevelModifierPlaceholder`)
replaces `_` only at the modifier body's **top level** (does not descend into
`if`/`for`/`while`/`unchecked`), while `Interface.lean:7068`
(`toCoreReplacingModifierPlaceholder?`) recurses. If any active path uses the
top-level-only variant, a modifier with `_` inside a conditional/loop drops the
function body. Likely masked by the recursive path — confirm which is live.

### B5 — `abi.encode` of narrow `uintN/intN` emits the raw stored word (medium)
`encodeStaticValue?` (`ABI.lean:153-207`) matches only `Ty.uint256/int256` and
calls `encodeWord value`; narrow types are normalized + `AbiCleanup`. If a value
with dirty high bits (from an `unchecked` op or `bytesN` masking) reaches
`abi.encode` without a forced cleanup, the encoded word carries the dirt, whereas
solc always cleans before encoding.

### B6 — Signed `checkedExp` overflow-detection order vs solc exp-by-squaring (low-med)
`checkedSignedExp` iterates linearly, validating each product against the
**int256** range and deferring narrow-`intN` bounds to `intCleanup`. If an
intermediate product overflows int256 but the final `intN` result is in range
under solc's squaring order (different intermediate grouping), the panic point
could differ.

### B7 — Transient storage (EIP-1153) clearing granularity (medium)
`clearTransient` (`Interpreter.lean:930`) sets `transient := {}`. Confirm
transient storage is cleared at **transaction end only**, not per message-call,
and that nested/re-entrant calls within one transaction observe accumulated
transient state.

### B8 — `require(cond, CustomError(...))` (0.8.26+) — **RESOLVED / faithful**
Initially flagged, then **verified faithful** by the second agent:
`Stmt.requireCustom` / `requireErrorExpr` (`Interpreter.lean:8122-8160`) evaluate
the second argument **unconditionally**, matching solc's `requireWithErrorFunction`
(docs `control-structures.rst:651-655`). No divergence — listed only to prevent
re-investigation.

### B9 — `le`/`ge` derived as `!(gt)` / `!(lt)`: check signed/unsigned operand mixing (low)
`Interpreter.lean:5449-5456` (and signed analog `:5490+`) compute `<=`/`>=` by
negating the strict comparison. Verify the signed path never routes a
`Value.word` (unsigned) operand through `sltWord`/`sgtWord` (and vice-versa) in
mixed `Value.int`/`Value.word` operand cases (the `Value.int, Value.word` arm at
`:5556+` defines only shift/exp — a stray comparison there would be a type-mismatch
revert vs a solc value).

### B10 — ABI-decode canonical-form validation of `intN` via `AbiCleanup.int` (low)
`AbiCleanup.accepts` for `int` (`Interpreter.lean:317-329`) accepts only if the
word equals its own canonical two's-complement re-encoding; `forceValue` reverts
**empty** otherwise. Confirm this matches solc's `validator_revert_t_intN`
(reverts empty on non-sign-extended input) — probe a non-sign-extended `int8` slot.

### B11 — Fixed-array-of-dynamic ABI encode head-offset base (low)
`encodeDynamicPayload?` fixedArray-of-dynamic (`ABI.lean:~241-258`) seeds the tail
offset at `wordBytes * size`. Verify the head region is exactly `N` words and that
this composes correctly when such a `T[N]` (T dynamic) is nested inside a dynamic
outer tuple — the relative offset base is easy to get wrong one level deep.

---

## C. Verified FAITHFUL (earned negatives — do not re-investigate)

- `&&` / `||` short-circuit (`Interpreter.lean:6166-6189`) — RHS not evaluated when decided.
- Loop `continue`/`break`: do-while `continue` → condition (`8593-8604`); `for`
  `continue` → post-statement (`8627-8631`); `break` → normal exit.
- `require(cond, CustomError/stringExpr)` — second arg evaluated unconditionally (= solc); see B8.
- `transfer`/`send` lowering (`Interface.lean:5423-5435, 4145-4157`): transfer
  failure forwards raw returndata; send yields the bool. (Gas-stipend representation
  differs — solc gas 0 relying on EVM stipend, solidity-lean passes 2300 — but gas is OOS.)
- `msg.sig` zero-pads short calldata (`Interpreter.lean:56-57`).
- `abi.decode` malformed data → empty revert (`Interpreter.lean:6369-6384`);
  bool/enum/narrow validation cleanups revert empty — matches solc validators.
- Catch-`Error`/`Panic` decode strictness matches solc's lenient decoders (modulo
  the already-recorded CB1); success-path return-decode failure reverts empty and
  is correctly not caught.
- Transient state vars: value-type-only, no initializer, Cancun-gated
  (`TypeCheck.lean:9398-9405`).

## Suggested priority

A2 (natural code style — fallback catch listed first — takes the wrong branch) →
A1 (the classic "try/catch doesn't protect against EOA targets" gotcha inverted) →
B1/B2/B3 (storage packing; unchecked-exp hang; narrow signed overflow) → A3 →
the remaining B candidates.
