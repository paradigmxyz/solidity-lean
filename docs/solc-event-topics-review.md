# solc event-topics / indexed-encoding divergence review

Scope: LOG **topic** side of event emission and the indexed/non-indexed split
in solidity-lean vs pinned solc 0.8.35 (legacy codegen). Sister review
`event-data-encoding` covered the non-indexed DATA payload; this pass targets
topic0, indexed value/reference encoding, anonymous handling, and the
accept/reject boundaries.

## Verdict: CLEAN NEGATIVE (confidence ~90%)

No divergence found. The topic path is a faithful transcription of solc's ABI
rules, and the hardest cases (indexed dynamic bytes/string, indexed array,
indexed struct, indexed struct-with-dynamic-member, indexed array-of-struct,
anonymous) are already exercised by an **in-gate** Forge fixture that pins
solc's exact topics, so those cases are ground-truth-validated, not merely
read.

## What was checked, against which code

### 1. topic0 = keccak256(canonical signature) — CORRECT
`EventDecl.abiSignature?` (Interface.lean:8187) builds `name(t1,t2,...)` from
`Ty.abiCanonical?` (Interface.lean:2426) — the **same** canonicalizer used for
function selectors (`FunctionDecl.abiSignature?`, :8076). Canonicalization is
correct: `uint`→`uint256`, `intN`/`uintN` kept, enum→`uint8` (:2477),
struct→tuple form `(...)` (:2474-2476), contract/UDVT ref→`address` (:2478;
UDVTs are pre-resolved to their underlying type by `resolveUserTypes` before
this point), dynamic array `t[]` (:2465), fixed array `t[N]` (:2468). topic0 is
attached in `EventDecl.toCore` (Interface.lean:19202) via
`Keccak.digestWord signature`, and set to `none` for anonymous.
Ground truth: fixture asserts `keccak256("Blob(bytes,string,bytes)")`,
`keccak256("Composite(uint8[],(uint8,uint16),bytes)")`,
`keccak256("Nested((uint8,bytes),bytes)")`,
`keccak256("PacketList((uint8,bytes)[],bytes)")` — all pass.

### 2. Anonymous events — CORRECT
- topic0 omitted: `toCore` sets `topic? := none` when `decl.anonymous`
  (Interface.lean:19208-19213); `encodeFields?` prepends only
  `decl.topic?.toList` (Interpreter.lean:5044) → no topic0.
- 4-indexed boundary: `EventDecl.indexedLimit` returns `4` for anonymous else
  `3` (TypeCheck.lean:11965-11967), enforced at :11993 with
  `invalidEventHeader "too many indexed event parameters"`. So non-anonymous
  with 4 indexed is rejected, anonymous with 4 accepted, anonymous with 5
  rejected — matches solc.
Ground truth: `Words(string indexed label) anonymous` → fixture asserts
`topics.length == 1`, `topics[0] == keccak256(bytes(label))`, empty data.

### 3. Indexed VALUE-type params → raw 32-byte topic — CORRECT
`abiEventTopic?` (Interpreter.lean:5005) for non-hashed types does
`bytesToWordBE (abiStaticBytes? ty value)`. `abiStaticBytes?`
(Interpreter.lean:4571):
- `uint256`/`int256`: full big-endian word (int values are already
  sign-extended 256-bit words → correct sign extension for `intN`).
- `bool`: clean 0/1 word (rejects dirty).
- `address`: left-padded 20-byte word.
- `fixedBytes size`: **left-aligned** (`wordToBytesBE size value ++ replicate
  (32-size) 0`, :4587-4588) → `bytesN` right-padded exactly as solc.
- enum indexed param is `uint256`-typed at the ABI boundary → raw left-padded
  word.
This is the same helper used on the validated ABI data/function-arg path, so
alignment and sign-extension are indirectly gate-covered.

### 4. Indexed DYNAMIC/REFERENCE-type params → keccak256(special encoding) — CORRECT
`Ty.isHashedEventIndexed` (Interpreter.lean:4622) selects
bytes/string(=`bytesCalldata`), dynamic array, fixed array, tuple(=struct).
`abiEventTopic?` hashes `abiEventIndexedBytes? padDynamic:=false`
(Interpreter.lean:4968), which implements solc's ABI-spec rule for indexed
non-value types exactly:
- top-level `string`/`bytes`: raw content, no length prefix, no padding
  (`bytes.map normByte`, :4974).
- struct: concat of members, each padded to a multiple of 32 (even a `bytes`
  member → `abiPadRightWord`, via `padDynamic:=true` in the tuple recursion
  :4998).
- array (dynamic or fixed): concat of elements each padded to 32, no length
  prefix (:4986-4992).
Ground truth (all pass in-gate): indexed `bytes`→`keccak256(key)`, indexed
`string`→`keccak256(bytes(label))`, indexed `uint8[]`→
`keccak256(abi.encode(uint8(1),uint8(2)))`, indexed `uint8[2]` likewise,
indexed struct `(uint8,uint16)`→`keccak256(abi.encode(...))`, indexed struct
with `bytes` member→`keccak256(abi.encode(uint8(5)) ++ padRightWord(body))`,
indexed `bytes[]`→`keccak256(padRightWord(c0) ++ padRightWord(c1))`, indexed
`Packet[]` (array of struct with dynamic member) — Lean matches solc on every
one.

### 5. DATA holds only NON-indexed params, ABI-encoded — CORRECT
`EventDecl.encodeFields?` (Interpreter.lean:5022) walks fields in declaration
order, routing `indexed` fields to topics and the rest to `dataTys/dataValues`,
then `abiEncodeValues? dataTys dataValues` (:5041) — standard head/tail
`abi.encode` of the non-indexed subset. Topic order (topic0 then indexed in
declaration order) and value order are preserved by the fold. No-param events:
`event E();` → LOG1 with topic0 only; anonymous no-param → LOG0 (fallback at
Interpreter.lean:7519-7524).

### 6. Argument evaluation order — CORRECT
`Stmt.emitEvent` (Interpreter.lean:8911) evaluates all argument expressions via
`Expr.evalListWithRuntimeOrder` before building/emitting the log — left-to-right
side effects match solc.

### 7. LOG0..LOG4 / topic-count limit — CORRECT
Total topics = `topic?.toList.length + indexedCount`, bounded by the
compile-time `indexedLimit` check (3/4). The emitted `Log.Entry.topics` list
maps 1:1 to the LOG_n opcode arity downstream (`logEntryToEvm`,
Interpreter.lean:2048).

## Fixtures backing this (all registered in tests/forge-harness/manifest.json)
- `event-indexed-dynamic` — the comprehensive topic fixture above.
- `event-emitter` — indexed `uint256` value-type topic + data.
- `event-error-shadowing` — event/error name resolution.

## Residual uncertainty (~10%)
Value-type topic variety NOT directly pinned by a dedicated fixture: indexed
`bytesN` left-alignment, negative `intN` sign-extension, indexed `enum`,
indexed `address`/`bool`. These are validated by *reading* `abiStaticBytes?`
(and its heavy reuse on the gate-covered ABI-data/function-arg path) rather
than by a dedicated event-topic assertion. A confirming probe would emit
`event V(bytes4 indexed b, int8 indexed n, MyEnum indexed e)` and diff topics;
I did not spin up the Lean interpreter for it because the shared helper is
already exercised elsewhere. No divergence is expected.
