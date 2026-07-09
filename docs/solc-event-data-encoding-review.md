# solc event emission review — topic0, non-indexed DATA section, split, anonymous

Adversarial review of solidity-lean's `LOG` emission against solc 0.8.35 (LEGACY
codegen, ABI coder v2). Scope: the parts NOT previously mined — topic0 (event
signature hash) canonicalization, the non-indexed DATA tuple encoding, the
indexed/non-indexed split, `anonymous` events, and topic counts. The indexed
reference-type topic encoding (`packedEncode`+keccak) was already reviewed clean
and is out of scope here.

Result: **CLEAN NEGATIVE.** No divergence found. Every checked axis matches solc,
including a bytecode-level confirmation of topic0 canonicalization for enum,
struct, `intN`, and `string`.

## Where the behavior lives (file:line)

- topic0 canonical signature string: `Ty.abiCanonical?`
  (`SolidCore/Solidity/Interface.lean:2426`), joined by
  `EventDecl.abiSignature?` (`Interface.lean:8155`), hashed in `EventDecl.toCore`
  (`Interface.lean:19162`) into `CoreEventDecl.topic?`.
- runtime split + encode: `EventDecl.encodeFields?`
  (`SolidCore/Solidity/Interpreter.lean:5002`), invoked by `Runtime.emitEvent`
  (`Interpreter.lean:7494`).
- indexed topic word: `abiEventTopic?` (`Interpreter.lean:4985`) →
  `abiEventIndexedBytes?` (`4948`) / `abiStaticBytes?`; hashed set is
  `Ty.isHashedEventIndexed` (`4602`).
- log materialization: `Event.toLogEntry` (`Interpreter.lean:830`).

## 1. topic0 canonicalization — CORRECT (bytecode-confirmed)

solc computes topic0 = `keccak256(FunctionType::externalSignature())`
(`libsolidity/ast/Types.cpp:3649`), which maps each parameter through its
*interface* type and `signatureInExternalFunction(false)`:
- enum → `interfaceType` = `encodingType` = `uint8`
- struct → `"(" + members.signatureInExternalFunction + ")"` (tuple, structs
  expanded by value, recursively; `Types.cpp:2528`)
- array → `base[...]` (`Types.cpp:1913`)
- contract → `address`; UDVT → underlying type

`Ty.abiCanonical?` (`Interface.lean:2426`) matches exactly: `bool`,
`address` (both address/address payable), `uintN`/`uint256`, `intN`/`int256`,
`bytesN`, `bytes`, `string`, `T[]`, `T[k]`, tuple/struct → `(...)`,
`enum → uint8`, `function → function`. UDVTs are rewritten to their underlying
type by `Ty.resolveUserTypes` (`Interface.lean:833`) *before* `abiCanonical?`
runs, so the `Ty.user => "address"` arm (`Interface.lean:2478`) only ever fires
for unresolved contract references — the correct `address` case.

Both indexed and non-indexed params are included in the signature
(`EventDecl.abiSignature?` iterates all `decl.params`), matching solc.

### Evidence — pinned solc 0.8.35 bytecode

Source: an event with an indexed narrow int, an enum, a dynamic struct, an
indexed string, and a signed int:

```solidity
event Mixed(uint8 indexed a, E e, S s, string indexed name, int128 z);
// E is enum{A,B,C}; S is struct{uint256 x; bytes b;}
event AllIndexed(uint256 indexed a, bytes32 indexed b);
event NoArgs();
```

`cast keccak` of the canonical strings solidity-lean derives:

| event | canonical signature (lean `abiCanonical?`) | topic0 |
|---|---|---|
| Mixed | `Mixed(uint8,uint8,(uint256,bytes),string,int128)` | `0x926c3bc7…975499` |
| AllIndexed | `AllIndexed(uint256,bytes32)` | `0x4b13b0ac…05a3cd2` |
| NoArgs | `NoArgs()` | `0xd144d9e3…ef576f5` |

Each of these 32-byte topic0 constants appears **exactly once** in
`solc-0.8.35 --bin-runtime` for the contract (grep confirmed, count = 1 each).
This proves solc canonicalizes `enum → uint8`, `struct → (uint256,bytes)`,
`int128 → int128`, `string → string` identically to solidity-lean.

## 2. non-indexed DATA section — CORRECT

`EventDecl.encodeFields?` (`Interpreter.lean:5002`) partitions fields by
`field.indexed`, collects the non-indexed field types (in declaration order — the
recursion prepends the current field to the tail result, preserving order) into
`dataTys`, and encodes them with `abiEncodeValues? dataTys dataValues`
(`Interpreter.lean:5021`). That is exactly solc's model: the non-indexed args are
ABI-v2-encoded as one tuple into `log` data, in declaration order. Dynamic
members (e.g. the `bytes` inside `S`, `string`/`bytes`/`T[]` data args) route
through the shared head/tail encoder (validated elsewhere). Only non-indexed args
reach `dataTys`; indexed args never enter the data tuple.

## 3. indexed/non-indexed split & topic ordering — CORRECT

`topics := decl.topic?.toList ++ indexedTopics` (`Interpreter.lean:5024`):
topic0 first (when present), then indexed args in declaration order. Value-type
indexed args → `abiStaticBytes?` padded word; reference-type indexed args
(`Ty.isHashedEventIndexed`: `bytesCalldata`/`string`, dynamic/fixed array, tuple)
→ `keccak(packed)` (`abiEventTopic?`, `Interpreter.lean:4985`). Note the core
`Ty` unifies `string` and `bytes` as `bytesCalldata` (`Interpreter.lean:74`), so
indexed `string`/`bytes` both hash the raw unpadded content — matching solc.

## 4. anonymous events — CORRECT

`EventDecl.toCore` sets `topic? := none` when `decl.anonymous`
(`Interface.lean:19169`). With `topic? = none`, `topics = indexedTopics` only —
no topic0 — and up to 4 indexed args become the topics. The no-field fast path in
`Runtime.emitEvent` (`Interpreter.lean:7500`, `fields.isEmpty && topic?.isNone`)
covers an anonymous zero-arg event → `log0` with empty data. An anonymous event
*with* fields still flows through `encodeFields?`, correctly omitting topic0.

## 5. special cases — CORRECT

- No-arg non-anonymous event (`NoArgs()`): `fields` empty but `topic?` is
  `some`, so it takes the `encodeFields?` branch → `topics = [topic0]`,
  `dataBytes = []` (`abiEncodeValues? [] [] = some []`). One topic, empty data. ✓
- All-indexed event (`AllIndexed`): `dataTys = []` → empty data; topics =
  `[topic0, a, b]`. ✓
- Topic-count limits (≤3 indexed non-anonymous, ≤4 anonymous) are solc
  compile-time checks; the runtime is fed only valid programs, so not a runtime
  divergence surface.

## Confidence

High. topic0 canonicalization is confirmed at the bytecode level against the
pinned solc for the trickiest cases (enum, dynamic struct, signed narrow int,
indexed string). The split/ordering/anonymous logic is verified by reading the
encoder, and the DATA tuple reuses the previously-validated `abiEncodeValues?`
path. No candidate divergences identified.
