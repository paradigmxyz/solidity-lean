# Deep review of MEMORY semantics, round 2 (solc 0.8.35 vs solidity-lean)

Follow-up to `docs/solc-memory-semantics-review.md` (round 1, which found **M1**:
memory→memory ref *assignment/declaration* deep-copies instead of aliasing —
now **IN-FLIGHT**, not re-reported here). This round goes deeper on the paths
round 1 flagged as "still-not-reached": **tuple-destructuring**, **the internal
function boundary**, **`abi.encode`/`keccak256` of nested memory aggregates**,
**`abi.decode` into nested memory**, and **string/bytes memory ops**.

Read-only. The corpus was **not** built or run. solc observables are PASS-verified
with pinned `solc-0.8.35+commit.47b9dedd` + `forge`. solidity-lean claims that require
execution are marked **INFERRED** (traced, not run).

---

## Executive summary

The abstract, id-keyed memory model (round 1) remains the frame: memory is
`MemoryMap := HashMap Nat Value`, a `memoryRef` is an allocation id, and nested
reference-type sub-objects are stored as their own `memoryRef` cells
(`memoryStoredValues`, `Interpreter.lean:1151`). This round confirms the model is
faithful for *values* but has **two more wrong-alias holes in code paths that
M1's fix will NOT touch**, plus **one spurious-revert hole** where the abstract
representation collides with the value-structural ABI encoder.

**NEW findings by reachability + severity:**

| Reachability | SOUNDNESS (wrong-alias / spurious-revert) | COMPLETENESS | UNTESTED |
|---|---|---|---|
| DIFFERENTIALLY-LIVE | **3 (M2, M3, M4)** | 0 | 0 |
| IMPORTER-MASKED | 0 | 0 | 0 |

Ranked (wrong-alias/wrong-value first):

1. **M2 — tuple-destructuring of memory refs deep-copies each component**
   instead of aliasing. `(a, b) = (x, y)`, `(a, b) = f()`, `(a, b) = (b, a)`,
   and the tuple *declaration* `(T memory a, ...) = (u, ...)` all land each
   memory-ref component as an **independent copy**. SOUNDNESS (wrong-alias),
   DIFFERENTIALLY-LIVE, solc **CONFIRMED** / solidity-lean **INFERRED**. **Separate
   code path from M1** (`writeTupleWithRuntime`/`assignTuple`, not
   `Stmt.assign`).
2. **M3 — assigning a memory ref into a memory AGGREGATE ELEMENT/FIELD
   deep-copies**. `s.field = a`, `arr[i] = a` store a *copy* of `a` into the
   element, so a later mutation of `a` is not seen through `s.field`/`arr[i]`
   (and vice-versa). SOUNDNESS (wrong-alias), DIFFERENTIALLY-LIVE, solc
   **CONFIRMED** / solidity-lean **INFERRED**. **Separate code path from M1** (the
   LHS is an index/member, so M1's `var = …` special case never fires).
3. **M4 — `abi.encode` / `keccak256(abi.encode(…))` of a ref-nested
   nested-dynamic memory aggregate spuriously REVERTS**. The value-structural
   encoder has no `memoryRef` case and the encode path never deep-materializes,
   so a memory value whose *elements* are themselves reference types (a local
   `bytes[]`, `string[]`, `uint[][]`, `T[]` of dynamic structs, or a struct with
   a dynamic-array field) hits unmaterialized `memoryRef` elements → encoder
   returns `none` → revert. solc encodes fine. SOUNDNESS (spurious revert /
   wrong observable), DIFFERENTIALLY-LIVE (for ref-nested memory values),
   solidity-lean **INFERRED**.

**Verdicts on the headline targets:**

- **Tuple-destructuring:** wrong (M2) — deep-copies, and via a code path M1's
  fix does not cover.
- **Internal boundary:** **faithful** for plain-var and array-element/struct-
  member arguments (the two-step arg-temp binding aliases them); ternary/call
  arguments share **M1's** root cause and fix. Not a separate finding.
- **Nested-memory `abi.encode` byte-fidelity:** the abstract model **does** bite
  here — not a byte mismatch but a spurious revert (M4).
- **`abi.decode` into nested memory:** faithful (decode builds inline value
  trees; see below).
- **String/bytes:** `bytes.concat`/`string.concat` faithful (fresh independent
  bytes); `string(bytesMemory)`/`bytes(stringMemory)` reinterpret should alias
  but is an **M1-family** shape (niche), noted below.

M1, M2, M3 share one root cause; a unified fix is recommended (see end).

---

## M2 — tuple-destructuring deep-copies memory refs

### solc ground truth (Forge, all PASS — `src/M3.sol`, `src/M4.sol`)

| Pattern | observable | verdict |
|---|---|---|
| `(a, b) = (x, y);` then `a[0]=7; b[0]=9` | `x[0]==7, y[0]==9` | **alias each** |
| `(uint[] memory a, uint b) = (u, 9);` then `a[0]=44` | `u[0]==44` | **alias** |
| `(a, b) = (b, a);` (with external alias `ca=a`), `a[0]=99` | `ca[0]==1, a[0]==99` | pointer swap |

solc lowers a tuple assignment to per-component `storeValue`s of the RHS
*pointers* (`libsolidity/codegen/ExpressionCompiler.cpp:377+`, `visit(Tuple…)`
+ the `Assignment` pointer store at `:303-333`). Each reference component is a
pointer copy.

### solidity-lean (traced)

- The importer lowers a tuple **assignment** to `Stmt.assignTuple` /
  `Stmt.assignTupleNested` (`Interface.lean:5704-5711`), and a tuple
  **declaration** to *default-init decls* + a `Stmt.assignTuple`
  (`tupleVarDeclCorePieces?`, `Interface.lean:5713-5725`).
- `Stmt.assignTuple` (`Interpreter.lean:7761`) evaluates the RHS tuple with
  ordinary eval (each memory-local component is **deref'd to an object**,
  `Expr.var` → `derefMemoryValue`, `:6010`), then `LValues.writeTupleWithRuntime`
  (`:7010-7019`) writes each value with `ResolvedLValue.write`.
- `ResolvedLValue.write` on a `local` name → `assignLocal?` (`:7720`, `:1241`),
  which for a memory-object value `memoryStoredValue`+`allocMemory`s a **fresh
  cell** (`:1249-1253`) → deep copy.

There is **no** `var = var` alias special case in the tuple path (that case
exists only in `Stmt.assign`, `:7743`). So `(a, b) = (x, y)` binds `a`,`b` to
fresh copies of `x`,`y`; the swap produces correct *values* (RHS is pre-evaluated
into temps) but breaks aliasing to any external pointer.

**Reachability:** DIFFERENTIALLY-LIVE — importer emits the tuple statements
verbatim, no aliasing rewrite. **Separate code path from M1** (`writeTuple…`
/ `assignTuple`, not `Stmt.assign`/`memoryVarDecl`) — M1's fix will not cover it
unless the fix also threads memory-ref values through the tuple write.

---

## M3 — memory ref stored into an aggregate element/field deep-copies

### solc ground truth (Forge, PASS)

| Pattern | observable | verdict |
|---|---|---|
| `s.inner = a;` then `a[0]=77` | `s.inner[0]==77` | **alias** |
| `arr[0] = a;` then `a[0]=66` | `arr[0][0]==66` | **alias** |

solc stores the RHS pointer into the memory slot for the element/field
(`ExpressionCompiler.cpp:303-333`, `MemoryItem::storeValue`).

### solidity-lean (traced)

`s.inner = a` lowers to `Stmt.assign (LValue.index (var s) 1) (Expr.var a)`
(struct member → index, `Interface.lean:1618-1625`). In `Stmt.assign`
(`Interpreter.lean:7717`) the `var = var` special case (`:7743`) requires the
**LHS to be a plain var** — here it is an index, so control goes to the general
path. The RHS `a` is deref'd to an object (`:6010`), and
`ResolvedLValue.valueIndex.write` (`:5736-5741`) calls `memoryStoreValue value`
(`:1178-1187`), which — because the value is a bare memory *object*, not a
`memoryRef` — `allocMemory`s a **fresh cell** and stores that ref into the
element. `s.inner`/`arr[0]` therefore point at an independent copy of `a`.

**Reachability:** DIFFERENTIALLY-LIVE. **Separate code path from M1** — the LHS is
an aggregate element (`ResolvedLValue.valueIndex`), never reached by M1's
var-LHS special case.

*Root-cause note:* if the RHS `a` flowed as `Value.memoryRef` (instead of being
deref'd), `memoryStoreValue` already aliases a `memoryRef` unchanged (`:1181`).
So M1/M2/M3 collapse to the same defect: **assignment RHS evaluation
materializes a memory ref into an object, and the store paths then treat a bare
object as "allocate a fresh copy."**

---

## M4 — `abi.encode`/`keccak256` of nested-dynamic memory spuriously reverts

### solc ground truth (Forge, PASS — solc encodes with no revert)

`abi.encode(bytes[] memory)`, `abi.encode(uint[][] memory)`, and
`keccak256(abi.encode(structWithDynamicArrayField))` all compile and run.
(`nestedEncode`, `twoDEncode`, `structDynEncode` in `src/M4.sol`.)

### solidity-lean (traced)

- A memory value with reference-type elements is stored **ref-nested**: e.g. a
  local `bytes[] memory bs` is `dynamicArray [memoryRef c0, memoryRef c1]`
  (`declareMemoryLocal` → `memoryStoredValues`, `Interpreter.lean:1151-1164`,
  `1298-1303`; element writes re-`allocMemory` too, `:5712`).
- `Expr.abiEncode` (`:6334-6340`) evaluates its args with ordinary
  `evalListWithRuntimeOrderFuel` — a **shallow** deref (`Expr.var` →
  `derefMemoryValue`, one level, `:1079/:6010`) — so the top array is
  materialized but its **elements stay `memoryRef`s**.
- The value-structural encoders (`abiEncodeStaticValue?`,
  `abiEncodeDynamicPayload?`, `:4572-4690`) match on concrete shapes
  (`Value.bytes`, `Value.dynamicArray`, `Value.tuple`, …) and have **no
  `memoryRef` case and no deref**. A `memoryRef` element matches nothing →
  `none` → `Expr.abiEncode` throws `typeMismatch` → **revert**. `keccak256`
  (`:6281`) evaluates the inner `abi.encode` first, so it reverts too.
- The elaboration does not help: `Args.toAbiEncode?` (`Interface.lean:4957-4963`)
  emits the raw arg expr (`Expr.var bs`) with no deep-materialization; there is
  **no** `derefMemoryValueDeep` on the encode path (the deep-deref call sites are
  storage stores and return collection only, `Interpreter.lean:3412…`,
  `7427/7447/7480/7500`).

**Scope / masking:** the divergence needs the encoded memory value to be
**ref-nested with reference-type elements**. Value-typed element arrays
(`uint[]`, `bytes32[]`) and single `bytes`/`string` encode fine (no sub-refs).
Decoded **parameters** are likely inline-masked (decode builds inline value
trees; a memory param carries an `AbiCleanup.memoryEager`/`abiLazy` that
`forceValue`s to the inline value, `:357-367`, `:1086`), so `abi.encode(param)`
may work. But a **local** nested-dynamic memory value, or one assembled in
memory, is ref-nested and would revert. `abi.encodePacked` of nested dynamic is
separately **rejected at analysis by both** (solc and solidity-lean AE1;
`Witness/AcceptanceBoundariesRound2.lean:182`) → masked; the hole is specific to
non-packed `abi.encode`.

**Reachability:** DIFFERENTIALLY-LIVE for ref-nested nested-dynamic memory
values; **INFERRED** (traced, not executed). **Recommended fix:** deep-deref the
encode/keccak arguments (`derefMemoryValuesDeep`) before `abiEncodeValues?`,
symmetric with the storage/return sites — or give the encoders a `memoryRef`
case.

---

## Internal function boundary — faithful (var/index args), M1-shared otherwise

### solc ground truth (Forge, PASS)

`mut(a)` (mutate `p[0]` in callee) → `a[0]==123`; `mut(arr[0])` →
`arr[0][0]==123`; `mut(c ? x : y)` → `x[0]==123`. Passing a memory ref aliases;
the callee's mutation is visible to the caller.

### solidity-lean (traced) — no separate finding

Internal-call arguments are bound in **two steps** (`Parameter.
toStorageAwareCoreArgDeclsEvaluated?`, `Interface.lean:9945-9990`): a temp
`_eval<i>` is declared from the argument expression, then the parameter is bound
from `_eval<i>`. For a memory parameter the temp is a `memoryVarDecl`, which
aliases when the argument is a plain **var** or an **index/member** (`Expr.index`
is handled by `memoryRefOrValueWithRuntimeOrder`, `Interpreter.lean:6689-6721`);
the runtime `internalCall` arm then passes the ref via
`evalRefArgWithRuntimeOrder` (`:6959-6971`). So `mut(a)` and `mut(arr[0])` **alias
back — faithful.** A **ternary/call** argument (`mut(c ? x : y)`) funnels through
the same `memoryVarDecl` that M1 fixes (conditional/call not yet ref-recognized)
→ **shared with M1**, not a new finding. Memory return of an internal fn and
"store ref into struct field then mutate" reduce to M1/M3 respectively.

---

## `abi.decode` into nested memory — faithful

`abiDecodeValueAt?` (`Interpreter.lean:4735-4845`) constructs **inline** value
trees (`Value.dynamicArray [Value.bytes …, …]`) directly from the byte payload —
no `memoryRef`s, no allocation — so a decoded nested aggregate is a materialized
value with correct element values and offsets; bounds/offset failures return
`none` → revert, matching solc's `validator_revert_*`. (The inline
representation is also why `abi.encode` of a freshly-decoded *parameter* tends to
work while a *local* is ref-nested — see M4 masking.)

---

## String/bytes memory operations

- **`bytes.concat` / `string.concat`:** `Value.concatBytes?`
  (`Interpreter.lean:248-255`) builds a **fresh** `List Byte` → a new independent
  `Value.bytes`. solc likewise materializes a fresh buffer. Forge confirms the
  result is independent of the inputs (`concatAlias`: mutating the source leaves
  the concat result unchanged). **Faithful.**
- **`string(bytesMemory)` / `bytes(stringMemory)`:** solc treats these as a
  zero-cost **reinterpret** — the result *aliases* the source (Forge
  `bytesToStr`: `bytes(s)[0]` reflects a post-conversion mutation of `b`). In
  solidity-lean both are `Value.bytes`, but a declaration `string memory s =
  string(b)` has a **conversion** RHS (neither `Expr.var` nor `Expr.index`), so
  `memoryVarDecl` falls to `declareMemoryLocal` → deep copy → no alias. This is
  the **M1 family** (an unrecognized memory-ref RHS shape), niche (requires
  mutating the `bytes` afterward and observing through the converted `string`).
  Flagged so M1's fix treats bytes↔string reinterpret as ref-preserving; not
  counted as a separate finding. **INFERRED.**
- **`bytes`/`string` indexing, `.length`:** element access deref's the ref
  (`Interpreter.lean:6588`); `.length` via `Value.length?` (`:202`). Faithful.
- **`push` to a memory `bytes`/`string`:** solc-rejected at compile → masked.

---

## Try/catch and modifiers (spot-checked)

Memory locals in try/catch clause bodies and across a modifier `_` are ordinary
memory locals in their frame; the try/catch return-value binding and modifier
inlining reuse the same `memoryVarDecl`/assignment machinery, so they inherit
M1/M2/M3 behavior rather than adding a new hole. No separate divergence found;
**UNTESTED** end-to-end (not probed this round).

---

## Recommended unified fix (for the M1 fix-agent to absorb M2/M3)

All three live wrong-alias findings have one root cause: an assignment/tuple/
element-store **evaluates a memory-ref RHS with the ordinary (deref'ing) path**,
then the store paths reallocate a bare object. A single fix covers M1+M2+M3:

1. Evaluate assignment / tuple-component / element-store RHS through the
   ref-preserving path (`memoryRefOrValueWithRuntimeOrder`, extended to
   `Expr.conditional`, memory-returning `Expr.call`, and bytes↔string
   reinterpret) so a memory-ref value flows as `Value.memoryRef`.
2. Ensure `memoryStoreValue`/`assignLocal?`/`writeTuple`/`valueIndex.write`
   **alias** a `Value.memoryRef` (they already do for the bare-ref case,
   `:1181`) instead of materializing+reallocating.

M4 is orthogonal: deep-deref (`derefMemoryValuesDeep`) the `abi.encode`/`keccak`
arguments before encoding.

---

## Checklist — covered vs still-not-reached

**Now covered (this round):**

- [x] Tuple-destructuring assignment of memory refs (M2)
- [x] Tuple-destructuring **declaration** of memory refs (M2, via `assignTuple`)
- [x] Tuple swap `(a,b)=(b,a)` (values correct; external-alias broken — M2)
- [x] Internal-boundary memory-arg aliasing (var/index faithful; ternary/call = M1)
- [x] Memory ref stored into struct field / array element (M3)
- [x] `abi.encode`/`keccak256` of nested-dynamic memory (M4 spurious revert)
- [x] `abi.decode` into nested memory (faithful, inline trees)
- [x] `bytes.concat`/`string.concat` aliasing (faithful)
- [x] `string(bytes)`/`bytes(string)` reinterpret aliasing (M1-family, niche)
- [x] Boundary temp-arg elaboration path (`toStorageAwareCoreArgDecls…`)

**Still not reached / deferred (honest):**

- [ ] Concrete solidity-lean execution of M2/M3/M4 (all INFERRED — corpus build/run
  out of scope).
- [ ] Byte-exact confirmation of `abi.encode` output *once M4 is fixed* (whether
  the deep-deref'd nested encoding matches solc byte-for-byte — expected yes, as
  the encoder is standard ABI, but unverified end-to-end).
- [ ] Memory in try/catch clause values and across modifiers, probed
  end-to-end (spot-reasoned only; inherits M1/M2/M3).
- [ ] Whether decoded memory *parameters* are truly abiLazy-inline in all cases
  (assumed; determines M4's exact blast radius — locals are live regardless).
- [ ] `mcopy`/byte-level layout — N/A in the id-keyed model (round 1).

---

## Cross-reference

- Round 1 (`docs/solc-memory-semantics-review.md`): M1 (memory ref
  assignment/declaration deep-copy) — **IN-FLIGHT**, not re-reported.
- Rounds 1–7 divergence docs did not touch the tuple/boundary/nested-encode
  memory paths — M2, M3, M4 are **NEW**.
- IN-FLIGHT (not re-reported): M1, DL1 (reverse-C3 storage/ctor order), V1
  (slice OOB), A1 (abstract interfaceId), EU1 (enum using-for dispatch).
