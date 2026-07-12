# R3: Type-Carrying Runtime Values — Design Note

Phase 2 of the rearchitecture (branch `rearch/value-typing`, base `73e1567`).
Three bug families share one root: runtime values are type-erased, so
downstream consumers re-infer types by enumerating `Value` shapes and dead-end
in `RevertData.typeMismatch` (Panic 0) on legal-but-unenumerated cases.

## 1. bytesN design: carried width via a new constructor (chosen)

**Chosen:** `Value.fixedBytes (size : Nat) (value : Word)` added to the `Value`
inductive (`Interpreter.lean`). The `Word` payload keeps the EXISTING internal
convention — right-aligned/numeric (meaningful bytes in the LOW `size` bytes;
left-alignment happens only at the ABI boundary) — the tag ADDS the width, it
never changes the word bits.

**Why not the threaded-type fallback:** proof churn turned out to be small
(see §5) — `FuelMonotonicity.lean` has only 4 `Value.`-adjacent case splits,
all on opaque accessors (`expectWord`, `asBytes?`) whose result SHAPE is
unchanged; `AdoptionLaws.lean`/`Interaction.lean` have none. The compiler
surfaces every exhaustive match; wildcard sinks were audited by hand
(`defaultLike`, `isMemoryObject`, `deleteZeroValue`, `derefMemoryValue*`,
`memoryStoredValue`, `coerceLike?`, `AbiCleanup.accepts`). The threaded-type
design would leave the #175 class open at every future call site.

**Migration rule (semantics-preserving):**
- Every WORD ACCESSOR unwraps the tag: `asWord?`, `asStorageWord?`,
  `expectWord`, `expectWordRaw` accept `Value.fixedBytes _ w` as `norm w`.
  Therefore any consumer that used to work on the bare `Value.word` keeps
  working bit-for-bit when a producer starts tagging.
- `Value.word` stays LEGAL for a bytesN value everywhere (dual arms at typed
  sinks); nothing REQUIRES the tag. The tag only enables intrinsic dispatch.
- Binary/unary ops keep operating on the raw word (identical results); bitwise
  and shift results RE-TAG with the operand width (`bitAnd/bitOr/bitXor/
  shl/shr/sar`, `~`); comparisons produce the plain bool `Value.word`.

**Producer inventory (all now emit the tag):**
- `fixedBytesIndex?` → `Value.fixedBytes 1 byte` (result type is `bytes1`)
- `fixedBytesCast?` / `fixedBytesFromBytes?` (explicit + literal casts)
- `Ty.storageValueFromWord?` `Ty.fixedBytes n` arm (storage scalar load)
- `packedStorageValueFromWord?` (routes through the same arm)
- `Ty.coerceValue?` `Ty.fixedBytes` arms (word + literal-`Value.bytes`)
- `Ty.defaultValue` (`Ty.fixedBytes size` → `fixedBytes size 0`)
- ABI decode `Ty.fixedBytes size` arm (`ABI.lean`)
- bytesN literals in lowering (`Expr.toCoreFixedBytesLiteralAs?` path,
  `Interface.lean`) — via the runtime cast nodes, already covered by
  `fixedBytesCast?`/`fixedBytesFromBytes?`/`Ty.coerceValue?`.
- `BinaryOp.apply`/`UnaryOp.apply` re-tag (see rule above)

**Consumer inventory (dispatch on the tag / accept it):**
- `Value.index?` — NEW intrinsic arm: `fixedBytes size w` → in-bounds byte
  extract (`Value.fixedBytes 1`), OOB → Panic 0x32. This closes the #175
  class: no caller-side routing to a dedicated `Expr.fixedBytesIndex` is
  needed for the value-typed path (ternary/call-result/any future shape).
- `Value.setIndex?`/`slice?`/`length?` — explicit no (unchanged semantics).
- `Value.coerceLike?` — `fixedBytes` template accepts `fixedBytes`/`word`
  (keeps template width); `word` template accepts `fixedBytes` (stays word —
  exact pre-change behaviour for untagged locals).
- `Ty.coerceValue?` — `Ty.fixedBytes` accepts both shapes, emits tagged.
- ABI encode head/packed/event-topic arms (`Interpreter.lean` +
  `ABI.lean` `encodeHeadValue?`-family): `Ty.fixedBytes size,
  Value.fixedBytes _ w` mirrors the word arm (left-aligned at boundary).
- `coerceStorageWordAs`/`coerceMappingKeyWordAs` — via `Ty.coerceValue?` +
  `asStorageWord?` unwrap (mapping-key left-alignment shift unchanged).
- `deleteZeroValue`/`defaultLike` — `fixedBytes size _` → `fixedBytes size 0`.
- `enumFromUIntValue`, casts (`uintCast?` etc.) — via `asStorageWord?`.

**Public-boundary normalization:** `Value.untagFixedBytes` strips the width
tag (recursively through arrays/tuples/abiLazy) in `FunctionDef.callBodyResult`
— the PUBLIC entry mapping only. The externally observable value of a bytesN
result stays the exact `Value.word` it always was (the contest observable
renders `Value.word w => "w:…"` and ~150 frozen lane evals destructure it;
`abiencode-lit-fixedbytes` caught this before the normalization). Internal-call
return capture does NOT route through `callBodyResult`, so width and ref
information keeps flowing across internal function boundaries where dispatch
needs it.

## 2. Storage-ref returns as uniform path-refs (#188)

**Lowering end (`Interface.lean`):** the storage-alias ASSIGNMENT intercept in
`Stmt.listToCoreWithInternalCallsWithRefs?` only matched a BARE-ident RHS
(`name = target` → `storageAliasAssign(From)`). A returned storage pointer is
rewritten to `retN = <rhs>` by `Parameters.returnAssignmentStmtsFromExpr?`, so
an INDEXED/MEMBER rhs (`arr[i]`, `m[k]`, `o.inner` — members are index
ordinals after `resolveStructs`) fell through to a VALUE load. New
`storageAliasAssignmentExprCore?` mirrors the WORKING decl dispatch
(`Expr.storageRefBranchAliasDeclCore?`) with the ASSIGN constructors:
- rhs ident → `storageAliasAssign` (state var) / `storageAliasAssignFrom`
  (ref local) [unchanged behaviour]
- rhs storage-ref-local path → `storageAliasAssignFrom(Path)` via
  `Expr.storageRefPathCore?`
- rhs state-var path → `storageAliasAssign(Path)` via `Expr.storagePathCore?`
- rhs ternary of two storage refs → `ifElse` over the two ASSIGN forms
  (mirrors the G#116 decl/arg form).
The interceptor now matches ANY rhs; non-storage shapes fall through to the
generic lowering exactly as before (interception is gated on
`StorageRefEnv.isStorageRef name`).

**Runtime end (`Interpreter.lean`):** `Value.coerceLike?` gets ref-repoint
arms — a `storageRef`/`storagePathRef` TEMPLATE meeting a
`storageRef`/`storagePathRef` VALUE re-points structurally (takes the new
ref) instead of `none` → Panic 0. `assignLocalRefAware?` already re-points on
ref VALUES; this closes the template side so `assignLocal?`-routed captures
cannot panic on a legal ref-for-ref assignment.

## 3. Storage materialization at value boundaries (#192)

Root: a bare state `bytes`/`string`/array/struct at a VALUE-USE boundary
lowers to `Expr.storage key`, whose eval is the HEADER word (length) by
convention (serving `.length`), so `asBytes?`/`abiEncodeValues?` get a word →
Panic 0. Fix has one shared helper at each end:

**Lowering (`Interface.lean`):** `materializeStorageValueUseCore` rewrites a
lowered arg core `Expr.storage key` → `Expr.storagePath key []` (the FULL
materializing read — `loadStoragePath` loads bytes/string → `Value.bytes`,
arrays → elements, structs → tuples). Applied uniformly to the argument(s) of:
`keccak256`, `sha256`/`ripemd160` (`externalHash`), `erc7201`,
`abi.encode`/`encodeWithSelector`/`encodeWithSignature`/`encodeCall`,
`abi.encodePacked`, `bytes.concat`/`string.concat`. Other core shapes pass
through untouched (`storageIndex`/`storagePath`/ref-locals already
materialize — verified by the BEFORE probes: mapping-value/struct-member
bytes already worked).

**Runtime (`Interpreter.lean`):** `Runtime.materializeForValueUse` =
deref memory refs deep + load `Value.storageRef name`/`Value.storagePathRef
name idxs` via `loadStoragePath`. Applied in the SAME builtin eval arms
(keccak256/erc7201/externalHash/concatBytes/abiEncode*/abiEncodePacked),
replacing the memory-only `derefMemoryValue(s)Deep`, so a storage ref VALUE
reaching a value boundary (ref-local flows) also materializes.

## 4. Verification plan
BEFORE probes (audit-r3): #175 ternary-base `(c ? a : b)[31]` Panic 0;
#188 t1–t5 (struct elem / call-lvalue / mapping / uint[] push / nested member)
all Panic 0, whole-var control t6 = 99 ok; #192 keccak(stored, len
5/31/32/33), sha256(stored), keccak(abi.encode(arr)), keccak(encodePacked(arr))
all Panic 0; controls (memory keccak, bytes(sstr), encodePacked(stored),
mapping/struct-member bytes) correct. AFTER: all fixed values match
cast/anvil; controls unchanged; bytesN preservation battery (c1–c8)
unchanged. Witness `SolidCore/Witness/ValueTyping.lean` + new Forge lanes pin
these.

## 5. Proof-churn sizing (measured before the edit)
- `FuelMonotonicity.lean`: 4 `Value.`-adjacent sites — case splits on
  `expectWord`/`asBytes?` results and a `[Value.word createResult.address]`
  literal; none case-split on the `Value` inductive itself. Expected churn:
  none-to-trivial (eval structure unchanged; only new match arms inside
  existing defs).
- `AdoptionLaws.lean`, `Interaction.lean`: zero `Value.` references.
- `Checked.lean`/`TypeCheck.lean`: zero `Value.` references.
- Witness files: constructors only (`Value.word` args/expectations); sites
  whose bytesN RESULTS become tagged get updated expectations — build
  surfaces each (`#guard` failures are compile errors).
- Interpreter/Interface/ABI: ~750 `Value.` occurrences, but the compiler
  finds every non-wildcard match; wildcard panic-sinks audited above.
This sizing is why the full-constructor design was chosen over the
threaded-type fallback.
