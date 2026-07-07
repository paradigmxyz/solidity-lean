# Compile-to-Yul readiness: mapping the source semantics for a composing Solidity→Yul lowering

Status: design/mapping study, 2026-07-06. Read-only analysis of
`SolidCore/Solidity/*` against `../evm-compiler` (Solidus) and the shared
`evm-interaction` alphabet. **No source changes proposed for this document to
land** — it is input for the orchestrator. All `file:line` anchors are as of
this read; the interpreter/ABI/Checked files and `Interface.lean`'s `NumberRat`
are being edited concurrently (Phase 5 / A1), so declaration names are the
stable anchor.

Scope: everything **except** the external-world/interaction boundary, which is
mid-refactor and out of scope. Where the boundary is load-bearing for a lowering
seam it is named, but no boundary refactor is recommended here.

---

## 0. What "composes with the evm-compiler proof" concretely requires

Solidus's crown theorem is `EvmCompiler.Solidus.compile_correct`
(`evm-compiler EvmCompiler/Correctness.lean:99`): for a decoded Yul object,
`rawObjectRun` **`ForwardRel`-refines** the open bytecode run, with
`truncated := Yul.FunctionsInteractionPrimitive.Truncated` and
`doneRel := ObservableDoneRel`. `ForwardRel`
(`evm-interaction/EvmCompiler/Simulation/Interaction.lean:1909`) has three
constructors: `truncated` (a source `done`-error tagged `truncated` relates to
*any* target — the source ran out of fuel, no claim), `done` (`doneRel` on the
two leaves), and `request` (**identical query on both sides**, and for **every**
answer the continuations are related). So a composing lowering step must be a
theorem of shape

```
ForwardRel truncatedSol solYulDoneRel
    (soliditySourceRun … initState)
    (rawObjectRun fuel ctx yulObject initState')
```

then `ForwardRel.trans` (`Interaction.lean:2244`) chains it with
`compile_correct`. `trans` carries one non-trivial side condition,
`hReflect`: if the Solidity leaf relates to a Yul `.OutOfFuel` failure, the
Solidity side must **already** have been truncated. Practically this is the
"the compiler cannot manufacture a fuel failure the source didn't have"
obligation, and it dictates that **fuel exhaustion in the source semantics must
be a distinguished, reflectable outcome** — exactly the `SolidityFailure.outOfFuel`
constructor Phase 5 is introducing (not an `Option`/`none`).

Three consequences fix everything downstream:

1. **Same query transcript.** The source execution and the emitted Yul must
   emit the *identical* `Query` sequence on identical answers. This is why the
   interaction-monad boundary (Phase 5) is a precondition for *any* lowering,
   and why the deterministic child-evaluation order is load-bearing.
2. **A done-relation on final states.** Not per-construct records (the deleted
   observation layer) — the *states themselves*. On the Yul side the comparison
   is `ObservableDoneRel` over `FinalStateObs` (`evm-compiler Solidus/Defs.lean:88`):
   code-erased `OpenWorld` equality (nonces, balances, storage, transient,
   code), `gasAvailable`, `activeWords`, `memory` bytes, `H_return`, and exact
   output bytes per halt kind. **The source's final state must be able to
   produce an `OpenWorld` and byte-exact output/revert data** to sit on the left
   of that relation.
3. **The alphabet and the entire Yul source semantics are frozen.**
   `Simulation/{Interaction,OpenWorld}.lean` and
   `Yul/{Syntax,EffectSemantics,InteractionSemantics}.lean` are in
   `evm-compiler benchmarks/frozen_manifest.txt`. New theorems compose *on top*
   via `trans`; they must not require editing those files. The `evm-interaction`
   extraction must stay byte-identical.

**The lowering target is not raw bytecode.** The top of Solidus is
`rawObjectRun` (`evm-compiler Solidus/SourceRun.lean:56`) / the canonical
`Yul.InteractionSemantics.exec` layer. A Solidity→Yul step only has to reach a
**Yul object** (dispatcher `Stmt` + function map, `EvmYul.Yul.Ast`); Solidus
carries it the rest of the way. That is the single most important fact for
sizing the future project: **we produce Yul, and inherit Solidus's ~7 verified
intermediate IRs below it** (Yul → Functions → Locals → Expressions → Structured
→ TypedCfg → Assembly → Bytecode; enumerated in §3). But "produce Yul" is itself
a tower, not one hop — see §3.

---

## 1. Internal-semantics map (the "rest")

### 1a. Surface AST — `Ast.lean` (441 lines)
Untyped, permissive, solc-shaped: full surface `Ty` grammar (arbitrary
`uint n`/`int n`, `fixed`/`ufixed`, `bytesN`, structs, mappings, function types
with data locations/visibility/mutability), `Literal` keeping numbers as **raw
strings** with denominations (`Ast.lean:140,165`), `Expr`/`Stmt` covering
try/catch, `unchecked`, modifier placeholder, and `inlineAssembly : String`
(opaque payload, `Ast.lean:293`). No expression-level type annotations — typing
is re-derived. This is a parser-frontend artifact; it is **not** the lowering
IR (see 2a).

### 1b. Elaboration — `Interface.lean` (~19.4k lines, `namespace Executable`)
Surface `SourceUnit` → the **interpreter's own core** (`Source.CoreExpr/CoreStmt/
CoreContract`, re-exported `Interface.lean:20`). There is no third IR: elaboration
emits exactly what the interpreter runs. The driver is `SourceUnit.toCoreContract?`
(`:19134`) → `ContractDecl.toCoreWithBasesAndUsing?` (`:18788`) →
`ContractDecl.toCoreFromOrders?` (`:18195`). Compute-once at elaboration:
- **Inheritance**: real C3 linearization (`mergeLinearizationsWithFuel?` `:17475`)
  for dispatch order; storage-append order (`storageOrder?` `:17422`).
- **Modifiers and internal calls are inlined** by placeholder/return substitution
  (`functionExpandModifiersToCoreWithInternalCalls?` `:10350`), bounded by
  `defaultInternalCallInlineFuel := 64` (`:10111`), producing `Stmt.captureReturn`
  scopes. The core has **no internal-call/modifier/`super`/inheritance
  construct at all**.
- **Selectors, event topics, external-fn-pointer address words** — keccak-computed
  at elaboration (`resolveSelectorsWithUnqualified` `:7733`,
  `resolveEventSelectors` `:7916`).
- **Storage slot/packing assignment** (`toCoreStorageFieldsFromSlot` `:17611`,
  `StoragePackingCursor` `:17530`, ERC-7201 `layoutBaseSlot?`), public-getter
  synthesis (`publicGetterBodyExpr` `:17772`), constant inlining
  (`inlineConstants` `:312`).
- **Type erasure** `Ty.toCore?` (`:2058`): `uintN/intN→uint256/int256`,
  `enum→uint256`, `struct→tuple` (field names erased), `string/bytes→bytesCalldata`,
  function types→`externalFunction`. Width survives as explicit core cast/cleanup
  nodes and packed-field metadata.
- **`NumberRat`** (`:2624`, mid-edit): non-negative rational constant folding
  `{num, den}`; `sub?` (`:2709`) fails closed on negative results; ops in
  `applyNumberRat?` (`:2791`). Fractional intermediates now fold (`1.5e18`);
  negative intermediates still don't. This is the recorded "rational constant"
  gap being narrowed.

The output `CoreContract` (`Interpreter.lean:7768` —
`storageFields/immutableFields/eventDecls/errorDecls/functions`) is a **closed
IR with zero surface references**. Two caveats: constructor entry points
**re-run the whole elaboration per construction** (`SourceUnit.constructContract?`
`:19145`), and `CheckedContract` deliberately keeps the surface `decl` beside
`core`.

### 1c. Typechecker — `TypeCheck.lean` (~12.8k lines)
Pure accept/reject: output is `Except TypeError CheckedSourceUnit` where
`CheckedSourceUnit = { source : SourceUnit }` (`:12116`) — **no typed
annotations flow downstream**; elaboration re-derives all types. Checks name
resolution, types, data locations, overrides, mutability (`view`/`pure`),
payable, try-catch shape, break/continue/placeholder placement. **Not
load-bearing for interpreter soundness** — the interpreter is defensively
dynamically typed (241 `typeMismatch` sites) — but load-bearing for
*acceptance* (the ~309 pinned-solc rejection lanes) and for justifying
elaboration assumptions (e.g. constant exprs contain no call nodes).

### 1d. Checked entry layer — `Checked.lean` (~2k lines)
`CheckedProgram` / `CheckedContract` bundle the invariant "typechecked +
type-resolved + elaboration succeeded"; runtime entries delegate to the core
(`CheckedContract.call?` → `Source.Contract.call?` on `contract.core`,
`:255`). Phase 5 has already added `*Tree` twins returning `SolI`
(`constructFromTree` `:473`, `callTree` `:504`, `CheckedProgram.callContractTree`
`:796`) beside the frozen `?` adapters.

### 1e. Value / type model — `Interpreter.lean` + `Shared/Word.lean`
- **`Word := Nat`** normalized mod `2^256` (`Shared/Word.lean:10,14`); every op
  lifts through `EvmYul.UInt256` (`liftEvmBinary` `:26`), so word arithmetic is
  **definitionally the pinned EVM package's**, round-tripped through `Nat`.
  Un-normalized `Nat` leaks only into intermediates; all stores/lookups normalize.
- **`Ty`** (`Interpreter.lean:68`): `bool|address|uint256|int256|fixedBytes n|
  bytesCalldata|externalFunction|fixedArray|dynamicArray|tuple` — **no sub-256-bit
  scalars**; narrow widths live only as cleanup annotations / packed-field widths.
- **`Value`** (`:91`): `word|int|bytes (List Byte)|externalFunction|fixedArray/
  dynamicArray/tuple (List Value)|storageRef String|storagePathRef String (List
  Value)|memoryRef Nat|abiLazy AbiCleanup Value`. Yul-friendly parts: `word`/`int`
  both carry a 256-bit two's-complement word (the signed tag is IR metadata a
  lowering erases); `externalFunction` uses solc's `addr·2^32+selector` word;
  `memoryRef Nat` is pointer-shaped. **Not** Yul-shaped: structural
  `fixedArray/dynamicArray/tuple` values passed by value as Lean lists; `bytes`
  as a byte list; `abiLazy` a deferred-cleanup wrapper value; `storageRef`/
  `storagePathRef` naming storage by **field-name String + typed index values**
  (slot recomputed per access); locals string-keyed (`Frame := List (String ×
  Value)`).

### 1f. State model
- **`State`** (`:760`): `storage : WordMap` (**already word-addressed**, `List
  (Word × Word)`), `transient : WordMap`, `immutables : ImmutableMap (String ×
  Value)` (**typed, name-keyed, not word-encoded**), `selfdestructs`,
  `externalInteractions : List ExternalInteraction` (recorded transcript),
  `events`. No balances/nonces/returndata in `State` — balances/codes/codehashes
  are read-only in `Context`; self-balance never mutates (the recorded
  balance-accounting gap). No returndata buffer (each call's result *is* a
  `Value.bytes`).
- **`Context`** (`:1488`): per-call constants (self/sender/value, block/tx env,
  account maps, contract-name maps, `gasleft` ambient constant, `childEvalOrder?`),
  plus the **oracle residue** `lowLevelCallResults/contractCreationResults`
  (`:1504`, Phase-5 stage-3 deletes).
- **`Runtime`** (`:885`): `state`, `locals`, and **two disconnected memory
  models**: (a) the live one — an **object heap** `memory : List (Nat × Value)`
  with `memoryRef` aliasing and deep deref (`allocMemory` `:961`,
  `derefMemoryValueDeep` `:1013`); (b) a **byte/EVM-shaped shadow**
  (`memoryByteMap`, `memoryFreePointer` starting `0x80`) written only at
  `newBytes`/`newDynamicArray` and **read nowhere** — vestigial footprint
  bookkeeping. See §4 finding **hinder-M**.
- **Rollback** is purely functional: `FunctionDef.callBodyResult` (`:7647`) maps
  `Result.reverted` to a `CallResult.reverted` carrying the **pre-call `State`
  snapshot**; storage/events/transient roll back by discarding. Pinned by
  `FunctionDef.call?_reverted_rolls_back` (`:7750`).

### 1g. Arithmetic
Exactly "Yul builtin + explicit overflow check". Unchecked → EvmYul-lifted wrap
(`addWord` …). Checked → test the mathematical result then throw
`RevertData.overflow = Panic 0x11` (`checkedAdd/Sub/Mul` `:4561`);
`checkedDiv/Mod` Panic 0x12 on zero; signed family via `Int` range check +
`signedToWord` (`:4630`), incl. MIN/−1 (`checkedSignedDiv` `:4659`);
`addmod/mulmod` (`:4675`). Sub-256-bit checked arithmetic = full-word op +
`uintCleanup?/intCleanup?` (Panic on out-of-range) — matching solc's cleanup
discipline. `BinaryOp` (`:4346`) is 20 ops incl. `shl/shr/sar`, dispatched
signed/unsigned by operand mode. **No fixed-point** (also unimplemented in solc).
No rationals in the interpreter. One naïveté: `checkedExp` is an O(exponent)
loop (`:4598`) — semantically fine, but see §4 **hinder-E**.

### 1h. Storage layout — spec-owned, solc-exact
`StorageLayout` (`:1182`) = `scalar|packedScalar|struct|fixedArray|dynamicArray|
bytes|string|mapping`; packing cursor reproduces solc sequential packing.
Slot derivation with **real keccak** (`mappingStorageSlot = keccak(key‖slot)`
`:1604`, `dynamicArrayDataSlot = keccak(slot)` `:1629`, ERC-7201 `erc7201Slot`
`:1597`). Packed read/write via bit-range ops (`:2224`); bytes/string short/long
form exactly (`storageBytesHeader?` `:2248`, long chunks at `keccak(slot)+i`).
One recursive load/store/clear family per layout
(`State.loadStorageLayoutAt`/`storeStorageLayoutAt`/deep-clear on shrink), and
the resolver `State.resolveStoragePathSlot` (`:3320`) that turns
`storagePathRef name indexes` into a concrete `(slot, layout)`. **This resolver
*is* the layout encoding `E : (typed access) → word slot` a lowering needs** —
but it is re-derived per access, not a standalone compiled artifact (§4
**help-S / neither-S**). Transient uses the same machinery on a separate map.
**Immutables are name-keyed typed values** (`ImmutableMap`), with no
code-substitution model — abstract vs the EVM's code-embedded immutables (§4
**hinder-I**).

### 1i. Control flow / functions / dispatch
`Expr` (`:4458`, ~60 ctors) and `Stmt` (`:6205`, ~55 ctors) are a **desugared,
monomorphic core**: storage/memory locations explicit, ABI/encode/cast/cleanup
nodes explicit. `Result` (`:6271`) is six-way `normal|returned|selfdestructed|
reverted|broke|continued`, each carrying `Runtime`. `FunctionDef` (`:7560`) →
`Contract` (`:7768`) a **flat `List FunctionDef`** found by name or selector
(dispatch resolved statically at elaboration). Try-catch
(`Stmt.tryExternalCall`/`tryContractCreate` `:6246`) branches on the
environment-answered result's `success`; catch dispatch matches
`Error(string)`/`Panic(uint)`/low-level bytes on the answer (`:6478`); the callee
**never executes** (open-world). Evaluation order: `ChildEvalOrder` (`:1483`)
with `yulCompatible := rightToLeft` (`:6047`), `effectiveChildEvalOrder`
defaulting to it; `unspecifiedOrders` is the **singleton** `[yulCompatible]`
(`:6053`) — deterministic in practice (§4 **help-O**).

### 1j. Events / errors
Events: `emitEvent` → `EventDecl.encodeFields?` (`:4252`) — topic0 = real-keccak
signature hash, indexed dynamic params hashed per ABI, non-indexed
ABI-encoded to data; anonymous = no topic0. `Event.toLogEntry` (`:742`) projects
to the shared `Log.Entry {address, topics, data}` — the EVM-observable form.
Reverts: **`RevertData`** (`:218`) is a *structured* sum
`empty|panic Word|error String|custom String (List Value)|raw (List Byte)`, not
bytes; the ABI layer encodes it to bytes at the boundary (`Contract.encodeRevertData?`
`ABI.lean:475`, real-keccak selectors). A lowering's done-relation must relate
this structured form to Yul's revert bytes (§4 **hinder-R**).

### 1k. ABI — `ABI.lean` (~1k lines)
Full head/tail spec encoding over core `Ty`/`Value`, `Bytes := List Byte`:
`isDynamicAbi`, `encodeStaticValue?`/`encodeDynamicPayload?`/`encodeValues?`,
fuel-bounded decode. Dispatch `Contract.callCalldataAtFromWithContext?` (`:669`):
4-byte selector → `findFunctionBySelector?` → **lenient** decode (lazy cleanups)
→ payable check → call → encode returns/revert; unknown selector → fallback;
short calldata → receive-or-fallback. Strict variant `decodeFunctionArgsStrict?`
(`:447`). Faithful; `string ≡ bytes` (no UTF-8 validation);
`List Byte`-of-`Nat` ↔ shared `ByteArray` bridged at the Phase-5 boundary.

---

## 2. Compile-to-Yul-composable analysis, area by area

The central alignment fact, from the three maps: **the interpreter is already
"Yul builtins + explicit checks over 256-bit words with word-addressed storage,
right-to-left deterministic evaluation, external effects as an interaction
tree."** That is a remarkably good starting point — most of the semantics is a
thin structured layer over exactly the primitives Yul exposes. The friction is
concentrated in a few representations that carry *typed/structural* information
Yul flattens, and in a few abstractions that erase information the done-relation
needs.

### 2a. The core language as the top lowering layer
**Helps.** The elaborated `CoreContract` is a genuinely clean IR candidate:
flat function list, word-valued expressions, explicit cast/cleanup nodes,
precomputed selectors/topics/slots, external effects already queries, zero
surface references, `Interpreter.lean` importing only `Shared.*` (clean
dependency floor). This is the natural anchor for the lowering's top layer.

**Hinders / seam risk.**
- **Internal calls and modifiers are inlined away before the core**
  (`:10350`, fuel 64). A faithful Yul lowering keeps Solidity internal functions
  as **Yul functions** (that is the whole point of the Functions layer below).
  The core has erased the very construct the first lowering layer would preserve,
  and **internal recursion is unrepresentable** (inline-fuel exhaustion →
  elaboration `none`). This is the single biggest structural mismatch: the
  source-of-truth "function" boundary is gone by the time we have the IR. See
  recommendation **D1**.
- **Constructor entry re-runs elaboration per construction** (`:19145`) — fine
  for an executable oracle, but it means "construct" is not a fixed IR artifact;
  a creation lowering theorem would want the elaborated creation-frame object
  once.
- String-keyed storage/locals at core level (`Expr.storage : String`,
  `Value.storageRef : String`) — a lowering must map these to slots/stack, which
  the layout resolver already computes but per-access (see 2d).

### 2b. Value / memory model vs Yul's word/memory model
**Helps.** `word`/`int` are 256-bit words; `memoryRef` is pointer-shaped;
`externalFunction` uses solc's exact word encoding.

**Hinders.** Structural `tuple/array` values and `bytes`-as-list are the classic
"abstract value that Yul represents as a memory region." A lowering to Yul must
pick a memory layout (head/tail, length-prefixed) for these and prove the
structural operations refine the pointer-arithmetic Yul emits. The interpreter's
**object-heap memory** (`memory : List (Nat × Value)` with aliasing) does **not**
correspond to Yul's flat `ByteArray` memory + free-memory-pointer at all — and
the byte-shadow that *would* correspond (`memoryByteMap`/`memoryFreePointer`)
is **dead** (§4 **hinder-M**). This is the memory-model translation layer the
lowering will need; the current abstract heap is convenient for execution but is
*not* the representation a memory-refinement proof wants. Per the roadmap this
is deliberately deferred (memory layout is not spec-owned; it reaches queries
only via ABI-encoded calldata bytes, which the ABI layer already concretizes).
The recommendation is only to **not entrench the dead byte-shadow** (§4 M).

### 2c. Arithmetic
**Helps, strongly.** Word ops are definitionally `EvmYul.UInt256` ops, and the
checked/unchecked split is already "wrapping builtin + explicit Panic guard" —
which is *exactly* what solc emits into Yul (`checked_add_t_uint256` = the
add plus a comparison-and-revert). This is close to a 1:1 lowering: each
`BinaryOp` arm maps to a Yul builtin call, each checked guard to the Yul
overflow-check snippet, each `*Cleanup` to the Yul cleanup function. The signed
tag on `Value.int` selects `sdiv/smod/slt/…` and is erased into the word.
**Neither.** `checkedExp` as an O(exponent) loop (§4 **hinder-E**) is a
performance/latitude wart, not a correctness one; a lowering would emit Yul's
`exp` builtin (environment/EVM-computed), so the source loop and the Yul builtin
must be proved equal — cheaper if the source uses a closed-form/`UInt256.exp`.

### 2d. Storage layout — the best-positioned seam
**Helps, strongly.** Storage is **already word-addressed** and the layout is
solc-exact with real keccak. Per the roadmap this is spec-owned and in scope.
The done-relation's `OpenWorld` storage is word→word; `State.storage` is
word→word; the snapshot is a near-direct read. This is the area where the source
semantics is *already* at the Yul level.
**Neither-S.** The layout encoding `E` (`resolveStoragePathSlot` `:3320`) exists
but is **re-derived per access** rather than materialized once as a
`CoreContract → (path → slot)` artifact. For a lowering proof you want a single
named total function (the "compiler-generated layout" the skill insists must
have a checked constructor). The logic is all present; it wants to be *lifted
out* into a standalone spec-owned definition (recommendation **P1**).

### 2e. Control flow / dispatch / try-catch
**Helps.** Structured control (`if`/`while`/`for`/`do-while`, six-way `Result`)
maps cleanly onto Yul's structured control (`if`/`for`/`switch`/`break`/
`continue`/`leave`) — the Structured layer in Solidus is precisely this
abstraction, so the shapes line up. Dispatch is a flat selector table → Yul
dispatcher `switch`. Try-catch is environment-answered (callee never executes),
matching Yul's open-world calls exactly — no nested-execution semantics to
reconcile.
**Hinders.** `broke`/`continued`/`returned`/`selfdestructed` as `Result` values
vs Yul's `Checkpoint`/`leave`/halt encoding is a control-encoding translation,
but a routine one (Solidus already relates structured control to label jumps).
The inlined modifiers/internal-calls (2a) are the real issue, not the loop forms.

### 2f. Events / errors
**Helps.** `Event.toLogEntry` already produces the EVM-observable
`{address, topics, data}`; a lowering emits Yul `log0..log4` and must show the
same topics/data — the encoding is already computed here with real keccak.
**Hinders-R.** `RevertData` as a *structured* sum must be related to Yul revert
*bytes*. The encoder exists (`encodeRevertData?`), so the done-relation is
"decode the source `RevertData`, ABI-encode, compare to Yul returndata" — fine,
but it means the public done-relation touches the ABI encoder. Keeping
`RevertData` structured is the right call for the source semantics (readable,
matches solc's error model); the lowering just carries the encode step. No
change recommended.

### 2g. Gas / fuel / truncation
**Helps.** `gasleft` is an ambient constant and the alphabet already reserves
`Query.resource gas`; Yul's `gas()` is `Query.resource .gas`, so un-deferring is
additive on both sides. Fuel exhaustion is becoming `SolidityFailure.outOfFuel`
(a distinguished, reflectable outcome), which is exactly what
`ForwardRel.trans`'s `hReflect` needs (§0). **This is the correct shape** — do
not let it regress to `Option`.
**Recorded residue (not to fix now):** `requestedGas` gas-key erasure (no-gas vs
`{gas: gasleft}` indistinguishable), and create `initCode` being source-canonical
(name-encoded) rather than compiled bytecode. Both are transcript-level
mismatches that resolve *at* the lowering (when creates carry real initCode and
gas is un-deferred) — they are correctly logged deferrals, and a lowering proof
would quantify over them or discharge them then.

---

## 3. The Solidity→Yul lowering as a stratified tower of intermediate IRs

**Correction to an earlier draft of this section.** A prior version proposed a
single new refinement layer ("elaborated `CoreContract` ⊑ Yul") for the whole
lowering. That badly understates the work and is not how Solidus is built. The
**composition seam** into `compile_correct` is indeed one new spine segment
(Solidity-source ⊑ Yul, chained by `ForwardRel.trans`), but the **proof** of
that segment must itself be a tower of intermediate IRs, each its own adjacent
`ForwardRel`, to be tractable — exactly as Solidus decomposes the *smaller*
Yul⊑EVM gap.

### What Solidus actually does for the smaller (Yul→EVM) gap

Verified by reading `../evm-compiler/EvmCompiler/`: `compile_correct`
(`Correctness.lean:99`) is **not** a Yul⊑EVM one-step proof. It is the transitive
composition (`ForwardRel.trans`, `Interaction.lean:2244`) of a chain of
per-IR refinements, one directory each:

```
Yul (canonical)                Yul/InteractionSemantics.lean
  ⊑ Functions                  Functions/Interaction*Preservation.lean   (hoist fns; stack-alloc layout)
  ⊑ Locals                     Locals/InteractionPreservation.lean        (named locals → stack slots)
  ⊑ Expressions                Expressions/InteractionPreservation.lean   (nested exprs → flat stack code)
  ⊑ Structured                 Structured/Interaction*Preservation.lean   (block/branch/loop/switch → labels)
  ⊑ TypedCfg                   TypedCfg/InteractionPreservation.lean       (structured → CFG + labels)
  ⊑ Assembly                   Assembly/InteractionPreservation.lean       (CFG → instruction list; + gasless→gasful bridge)
  ⊑ Bytecode / EVM.X           Assembly/InteractionBytecode.lean, GasfulBridge
```

~7 intermediate IRs for a gap where **Yul already provides** words, memory,
storage, keccak, and calls as primitives. Two structural lessons for us:
- **Each seam introduces exactly one abstraction** and carries its **own
  done-relation**, which grows more machine-specific downward: `Functions`
  `StateOutcomeRel layout suffix` (stack layout appears), `Locals`/`Expressions`
  `OutcomeRel baseStack`/locals-`Ctx`-keyed (stack slots appear), `TypedCfg`
  `SegmentDoneRel` over CFG exit tokens (labels appear). The high, abstract
  done-relations near the top compare *values*; the low ones compare *stacks and
  layouts*. Same transcript throughout (`Query` alphabet is invariant).
- Truncation (`OutOfFuel`) is threaded through every seam and reflected by each
  `trans`'s `hReflect` — the discipline is uniform, one instrument per layer.

### Why Solidity→Yul is a *larger* gap, and its tower is *taller*

Solidity is much higher-level than Yul. Yul is not the problem to *implement*
(it already has memory/storage/keccak/call builtins); the job is to **lay out
high-level constructs onto those builtins** — and that layout decomposes into
several independent abstractions, each of which wants its own IR and its own
refinement to stay tractable. The elaborated `CoreContract` is **not the top of
one short hop**; it is a partly-collapsed IR that a real tower would *un-collapse*
into distinct layers. The realistic tower, top-down from `CoreContract` to a Yul
object:

```
        (frontend, trusted or separately-verified — NOT the lowering spine)
        Surface AST → TypeCheck (acceptance) → Elaboration → CoreContract

  ── the new lowering spine: Solidity-source ⊑ Yul, decomposed ──

  Sd  DISPATCH / OBJECT layer     CoreContract (flat FunctionDef list + selector table,
                                   storage/event/error decls, immutables)
      abstracts: the contract-as-callable — one public entry answering calldata.
      seam Sd→Sc: selector table → Yul dispatcher `switch`; public fns → external
                  entry wrappers (ABI decode args / encode returns around the call);
                  receive/fallback arms; constructor → creation object.
      done-rel: OpenWorld + exact output/revert bytes + logs (the TOP relation,
                = the composition seam's done-rel; compares observable values, no layout).
      size: MEDIUM. Mostly a table→switch structural map; the ABI wrappers are
            shared with Sb. Hardest part is receive/fallback/constructor corner cases.

  Sc  CALLING-CONVENTION / FUNCTION layer   functions with internal calls + params/returns
      abstracts: the internal-function boundary and internal (possibly recursive) calls.
      seam Sc→Sb: each Solidity internal function → a real Yul function; internal
                  call → Yul function call; named returns / multiple returns → Yul
                  return-var convention; modifier wrappers → caller/callee split.
      done-rel: OpenWorld + return values (as words/memory refs) + control outcome
                (normal/return/revert), quantified over the call graph by induction
                on source fuel / the evaluation derivation.
      size: LARGE and HARDEST — and today it has NOTHING to refine, because
            elaboration has already INLINED internal calls and modifiers away
            (fuel 64) before CoreContract exists (§2a, D1). This layer's source IR
            must be RECONSTRUCTED (keep functions as functions upstream) or the
            layer is impossible and recursion stays unsupported. See D1.

  Sm  MEMORY-LAYOUT layer         structural values (tuple/array/bytes/string, memoryRef)
      abstracts: aggregate values as regions of a flat byte memory.
      seam Sm→(word/byte ops): structs/arrays → head/tail + length-prefix layout on
                  Yul memory; free-memory-pointer discipline (the FMP word lives
                  at 0x40 and initially points to 0x80, the start of free memory);
                  memoryRef →
                  concrete offset; copy/allocation → mstore/mload sequences.
      done-rel: value ≅ (region of the flat `ByteArray` memory) under a memory
                invariant; final `memory`/`activeWords` match the Yul done-rel's
                memory fields.
      size: LARGE. Full translation layer — the interpreter's object-heap memory
            (List (Nat × Value) with aliasing) does NOT correspond to Yul memory
            at all, and the byte-shadow that would is DEAD (§4 hinder-M). New model,
            new invariant, per-type layout proofs. Deliberately roadmap-deferred.

  Sy  STORAGE-LAYOUT layer        typed storage paths (mappings/arrays/packing)
      abstracts: typed field/mapping/array access as slot arithmetic + keccak.
      seam Sy→(sload/sstore): storagePathRef → slot via the materialized encoding E
                  (keccak(key‖slot), keccak(slot)+i, packed bit-ranges, short/long
                  bytes); read/write/deep-clear → word ops.
      done-rel: typed storage state ≅ word storage under E; = the OpenWorld storage
                field. NEAR-IDENTITY on our side — storage is already word-addressed,
                E already computed (needs materializing, P1).
      size: SMALL–MEDIUM, the CHEAPEST seam. Our representation already lives at
            the target. Mostly: lift E out (P1) + prove the per-access path = E.

  Sx  ABI-CODEC layer             encode/decode of args/returns/revert/events
      abstracts: values ↔ ABI byte strings (head/tail, dynamic offsets, selectors).
      seam Sx→(byte/memory ops): encodeValues/decodeArgs → Yul ABI encode/decode
                  builtins over memory; RevertData → error/panic/custom bytes;
                  event fields → topics + data bytes.
      done-rel: produced bytes byte-identical to Yul's; already computed here over
                List Byte (bridge to ByteArray). Interlocks with Sm (codec writes
                to the memory model) and Sd (dispatch uses the codec).
      size: MEDIUM. The spec logic exists and is faithful; the work is relating it
            to Yul's codec over the concrete memory model (so it rides on Sm).

  Sk  ARITHMETIC / CONTROL layer  checked/unchecked word ops; if/for/while; require/revert
      abstracts: (almost nothing — this is where we already ARE at Yul level).
      seam Sk→Yul: BinaryOp → Yul builtin; checked guard → Yul overflow-check
                  snippet + Panic; *Cleanup → Yul cleanup fn; structured control →
                  Yul if/for/switch/break/continue/leave; Result(broke/continued/
                  returned) → Yul control encoding.
      done-rel: word-for-word equality; structured-control outcome match.
      size: SMALLEST, near-1:1. Word ops are DEFINITIONALLY EvmYul.UInt256 (§2c);
            checked = wrapping-builtin + explicit Panic = solc's own Yul shape;
            control shapes line up with Yul's (and with Solidus's Structured layer).
```

These are not a strict linear stack — `Sm`, `Sy`, `Sx`, `Sk` are **largely
orthogonal abstractions** that a real compiler applies together, and a proof
engineer would sequence them as independent refinements (or bundle memory+ABI,
since ABI encoding *targets* the memory model). `Sd`/`Sc` are the genuinely
*vertical* ones (contract→functions→function bodies). A plausible ordering that
keeps each adjacent theorem to one abstraction: **Sy (storage) and Sk
(arith/control) first — cheap, our IR is already there — then Sx+Sm together
(codec on memory), then Sc (calling convention), then Sd (dispatch/object) on
top.** The composition seam's done-relation is `Sd`'s top relation (observable
`OpenWorld` + bytes + logs); the internal seams' done-relations are progressively
more concrete (memory offsets, slot arithmetic, stack-free but layout-explicit).

### Where the elaborated CoreContract actually sits

**Not at the top of a short hop — mid-tower, with some layers already collapsed
and one prematurely destroyed.** Concretely:
- CoreContract has **already applied Sy-input and Sk-input shape**: storage
  access is explicit typed paths (good — Sy's source), arithmetic is explicit
  word ops with cleanup nodes (good — Sk's source). For these seams the core is
  a clean, aligned top IR.
- CoreContract has **already partly collapsed Sm**: values are still structural
  (`tuple/array/bytes`), so Sm's *source* is present — but memory is an object
  heap, so there is representation work, not just a layout choice.
- CoreContract has **destroyed Sc's source**: internal calls and modifiers are
  inlined away and recursion is unrepresentable (§2a). The calling-convention
  layer has **no IR to refine** unless a function-preserving representation is
  kept upstream. This is the tower's structural break, not a detail.
- CoreContract **is** roughly Sd's source (flat function list + selector table),
  so the dispatch layer sits naturally on it.

So the honest picture: the current core is a good **Sy/Sk/Sd** anchor, an
**adequate-but-heap-mismatched Sm/Sx** anchor, and a **broken Sc** anchor. A
real tower would either (a) re-introduce a function-structured IR above the
current inlined core, or (b) explicitly scope the lowering to non-recursive
internal calls and accept inlining — a stated fragment, which the
verified-compiler discipline warns against doing silently.

### Hardest seams (ranked)

1. **Sc (calling convention / function boundary)** — hardest, and currently
   *impossible on the existing IR* because the boundary is inlined away and
   recursion is unrepresentable. Needs the source IR reconstructed (D1). Its
   proof is the induction-on-source-fuel/derivation over the call graph — the
   one place the skill insists you must not use an "all callees preserve"
   oracle.
2. **Sm (memory layout)** — full translation layer; the object-heap memory has
   no correspondence to Yul's flat bytes, and the would-be byte model is dead
   code. New model + invariant + per-type layout proofs. Interlocks with Sx.
3. **Sx (ABI codec) on the memory model** — faithful spec exists, but relating
   it to Yul's codec over concrete memory rides on Sm and touches the public
   done-relation (revert/return bytes).

Cheapest, by contrast: **Sy (storage)** and **Sk (arithmetic/control)** — our
representation already lives at the Yul level for both.

---

## 4. Findings ledger (help / hinder / vestigial)

- **help-A (arithmetic)** — word ops are definitionally `UInt256`; checked =
  wrapping-builtin + explicit Panic guard = solc's Yul shape. Near-1:1 lowering.
- **help-S (storage)** — word-addressed, solc-exact, real keccak; storage
  done-relation is near-direct. Best-positioned seam.
- **help-O (order)** — deterministic right-to-left `yulCompatible` evaluation
  already chosen and load-bearing; makes the query transcript well-defined.
- **help-G (fuel/gas)** — `outOfFuel` distinguished outcome matches
  `ForwardRel.trans` `hReflect`; `Query.resource gas` reserved on both sides.
- **help-C (control)** — structured control + flat selector dispatch +
  environment-answered try-catch line up with Yul's structured control and
  open-world calls.
- **neither-S (layout artifact)** — `E` exists but is re-derived per access, not
  a materialized spec-owned function. → **P1**.
- **hinder-D1 (function boundary)** — modifiers/internal-calls inlined,
  recursion unrepresentable, before the core IR exists. The one deep mismatch. → **D1**.
- **hinder-M (memory)** — live memory is an object heap unlike Yul's flat bytes;
  the byte-shadow that *would* correspond is **dead code**. → **M** (delete/keep-out).
- **hinder-I (immutables)** — name-keyed typed values, no code-substitution
  model; abstract vs EVM code-embedded immutables. Lowering-era concern; note only.
- **hinder-R (revert)** — structured `RevertData` vs Yul bytes; encoder exists,
  done-rel carries the encode. Keep structured; note only.
- **hinder-E (exp)** — `checkedExp` O(exponent) loop; lower to Yul `exp`, prove
  equal. Cheaper against a closed-form. Note only.
- **vestigial-1** — **~14 dead classifier enums** (observation-era vocabulary
  outliving Phase 4): `LowLevelCallEvaluationStatus` (`:6085`),
  `ContractCreationEvaluationStatus` (`:6096`), `ShortCircuitDecision` (`:6107`),
  `TerminalEvaluationKind/Status`, `RequireCheckKind`, `RevertPayloadKind`,
  `IfBranchSelection`, `WhileLoopStep/ForLoopStep`, `EvalMode`,
  `TryExternalCallEvaluationStatus/TryContractCreateEvaluationStatus`,
  `FunctionEntryKind`, `ExternalResolutionKind`, `StorageFieldAccessKind`,
  `ResultMode`, `CallExitMode` — zero non-definition references. → **V1**.
- **vestigial-2** — the dead byte-memory shadow (= hinder-M). → **M**.
- **vestigial-3** — `ChildEvalOrder.unspecifiedOrders` singleton +
  `callUnspecifiedResults`/`CallsUnspecified` machinery: the unspecified-order
  latitude has collapsed to a single deterministic order but the quantification
  scaffolding remains. → **V3** (evaluate; low priority).
- **vestigial-4** — end-of-file example/witness defs in `Interpreter.lean`
  (`compositionalControlExample … writesThenRevertsCall`, `:7939–8113`) living
  in the semantics file rather than `Witness/`. → **V4** (trivial move).
- **clean** — zero `partial`/`sorry`/`axiom` in `Interpreter.lean`; no
  nondeterminism (single deterministic evaluation order); rollback purely
  functional and pinned by a theorem.

---

## 5. Recommended prep refactorings

Separated into "worth doing now (during this cleanup, while the files are in
motion)" and "defer to the lowering project." Each anchored to code. **None of
these should race the in-flight Phase 5 / A1 edits** — the ones touching
`Interpreter.lean`/`Interface.lean` should land after Phase 5 settles or be
scoped to untouched regions; that ordering note is part of each item.

### Do now (cheap, and now beats later)

**N1 — Delete the ~14 dead observation-era classifier enums (vestigial-1).**
*Rationale:* they are the exact "speculative interface built for a future proof,
used in zero theorems" the roadmap and skill both say to delete — a second,
smaller instance of the already-deleted observation layer. Leaving them invites
someone to "maintain" them per semantic change. *Cost:* ~1 hour; pure deletion,
build-checked (they have no non-definition references). *Now-beats-later:* Phase
4 already tuned the deletion tooling for exactly this pattern; the tree is
already being churned so the diff is cheap to review. *Ordering:* independent of
Phase 5's live edits (these enums are not on the SolI path) — but coordinate to
land after Phase 5 to avoid merge noise. Anchor: `Interpreter.lean:6085–7709`
enumerated in §4 vestigial-1.

**N2 — Retire the dead byte-memory shadow, or mark it explicitly (hinder-M / V2).**
*Rationale:* `memoryByteMap`/`memoryBytesUsed`/`memoryFreePointer`/
`memoryAllocations` with readers `loadMemoryByte?/readMemoryBytes?` that have
**zero call sites** are dead weight that will actively **mislead** the lowering
project — it looks like the Yul-shaped memory model but is unwired and only
partially populated. Either delete it, or (if the alloc-limit guard genuinely
needs the counter) reduce it to just the counter with a comment saying it is
*not* a memory semantics. *Cost:* 1–2 hours (verify the alloc-limit guard's real
dependency first). *Now-beats-later:* the future memory-refinement layer will
want to *build* the real byte model; a half-built impostor in `Runtime` is worse
than nothing. *Ordering:* `Runtime` is on the Phase-5 path — do after it settles.
Anchor: `Interpreter.lean:676, 924, 940, 944, 961`.

**N3 — Move the in-file example defs to `Witness/` (V4).**
*Rationale:* the roadmap's "no mixed-concern file" rule; `compositionalControlExample
… writesThenRevertsCall` are witnesses living in the semantics module. *Cost:*
~30 min, verbatim move (Phase-3a pattern). *Now-beats-later:* trivial now, and
keeps the semantics file to semantics as the lowering carves it up. Anchor:
`Interpreter.lean:7939–8113`.

**N4 — Coarse import edge: `Ast.lean` imports `ABI.lean` (hence the whole
interpreter) for just `Word`/`Byte`/precompile names.**
*Rationale:* the surface AST should not depend on the interpreter; this inverts
the clean core-first dependency floor and would force the lowering's frontend to
drag the interpreter. *Cost:* ~1 hour — point `Ast.lean` at `Shared/Word.lean`
(and a small precompile-names module) instead of `ABI.lean`. *Now-beats-later:*
the dependency graph is being actively reshaped this cleanup; fixing the edge now
avoids re-plumbing later. *Ordering:* `Ast.lean` and `ABI.lean` are both touched
by concurrent agents — confirm current imports before editing; low urgency, can
wait for Phase 6. Anchor: `Ast.lean:8`.

### Consider now (higher value, higher care — flag for the orchestrator)

**P1 — Lift the storage-layout encoding `E` into a standalone spec-owned
function (neither-S).** *Rationale:* the lowering's storage seam needs a single
named total `CoreContract →ᴱ (storage path → word slot + packing)` with a checked
constructor (the skill's "compiler-generated evidence must be constructed").
Today the logic lives inside `resolveStoragePathSlot` (`:3320`) and the
elaboration-side slot assignment (`toCoreStorageFieldsFromSlot` `Interface.lean:17611`),
re-derived per access. Extracting it now — as a definition the interpreter
*uses* (proving the per-access path equals `E`) rather than a parallel copy —
both cleans the semantics and pre-builds the lowering's most important artifact.
*Cost:* 1–2 days; must be behavior-preserving (corpus is the arbiter) and must
not race Phase 5's storage reads. *Now-vs-later:* genuinely optional now; the
logic is correct and present. Do it now only if the orchestrator wants the
storage seam de-risked early; otherwise it is a clean early task for the lowering
project. Recommend: **flag, lean toward deferring** unless storage is the first
lowering layer.

**D1 — The function-boundary gap destroys an entire tower layer's source IR —
DESIGN NOTE, not a refactor to execute now.** *Rationale (sharpened per §3):*
this is not merely "one deep mismatch" among the seams — it is the tower's
**structural break**. The realistic Solidity→Yul tower has a dedicated
**calling-convention layer Sc** (Solidity internal functions → real Yul
functions; internal calls → Yul calls; modifiers → caller/callee split), whose
entire *point* is to preserve and lower the function boundary, and whose
correctness proof is the induction-on-source-fuel over the call graph. That
layer needs a function-structured source IR to refine. The current elaboration
**inlines internal calls and modifiers away (fuel 64) before `CoreContract`
exists**, so Sc has **nothing to refine** and **recursion is unrepresentable**
end-to-end (inline-fuel exhaustion → elaboration `none`, silently rejecting deep
or recursive call graphs). Every other seam (Sy/Sk/Sm/Sx/Sd) has a viable source
in the current core; Sc alone does not. *Options:* (a) keep inlining and scope
the lowering to non-recursive internal calls — a *stated accepted-fragment*,
which the verified-compiler discipline permits only if named in the theorem, not
smuggled; (b) keep a function-structured IR **above** the inlined core (a new top
layer that lowers to today's core by an inlining refinement, or replaces it) so
Sc has a boundary to preserve. *Recommendation:* **do NOT build it now** —
speculative construction violates the roadmap's "no new speculative interfaces,"
and the right design belongs to the lowering project. But **record it now, as
the #1 lowering-design question**, and additionally **treat the current
recursion/deep-call-graph rejection as a candidate recorded semantic gap** (a
paired lane would pin whether solc accepts programs this elaboration silently
drops) — because that boundary limits what the *current* semantics can claim
irrespective of any lowering. *Cost now:* zero (documentation). *Cost later:*
large, load-bearing, and gating the hardest seam.

**V3 — Evaluate collapsing the `unspecifiedOrders` scaffolding (vestigial-3).**
*Rationale:* the latitude machinery (`callUnspecifiedResults`,
`CalldataCallUnspecified`, the `unspecifiedOrders := [yulCompatible]` singleton)
quantifies over one deterministic order. If the design intent is "evaluation
order is fixed and Yul-compatible" (which the lowering *needs*), the
quantification is dead generality; if it is "we might re-open order latitude,"
it should be documented as such. *Cost:* ~half a day to trace all users and
decide. *Now-vs-later:* low priority; harmless. Flag, likely defer. Anchors:
`Interpreter.lean:6053, 7735, 7742`, `ABI.lean:703, 711`.

### Defer to the lowering project (do NOT build now)

- **Memory-refinement layer** (structural values / `bytes` → flat Yul memory +
  free-memory-pointer). Deliberately deferred per roadmap (memory layout is not
  spec-owned). Build the real byte model *in the lowering*, not now.
- **`RevertData` → bytes done-relation** (hinder-R): the encoder exists; the
  relation is a lowering-proof artifact.
- **`checkedExp` → Yul `exp`** equality (hinder-E): lowering-proof artifact;
  possibly simplify the source to a closed form *then*.
- **Immutables code-substitution model** (hinder-I): lowering-era; the
  name-keyed abstraction is fine for the source semantics.
- **Un-deferring `gasleft` / real create initCode**: recorded gaps; resolve at
  the lowering when gas/creation transcripts must align byte-for-byte with Yul.
- **Elaboration correctness** (surface → core): either a separate obligation or
  surface-as-trusted-input (matching how Solidus treats solc's Yul emission).
  Not a source-semantics cleanup task.

---

## 6. Summary

**Layer map (§3):** import Solidus's Yul→bytecode tower (frozen) — we emit a Yul
object and inherit ~7 verified IRs below it. The Solidity→Yul gap is a **single
composition seam** (Solidity-source ⊑ Yul, chained into `compile_correct` by
`ForwardRel.trans`) whose **proof is its own stratified tower**, because
Solidity→Yul is a *larger* semantic distance than the Yul→EVM gap Solidus itself
decomposed into ~7 IRs. Ordered intermediate IRs (top-down from the elaborated
core to Yul), each an adjacent `ForwardRel` with its own done-relation:
- **Sd — dispatch/object**: selector table → Yul dispatcher `switch`. done-rel:
  `OpenWorld` + output/revert bytes + logs (this *is* the composition seam's
  top done-relation — observable values, no layout). MEDIUM.
- **Sc — calling convention / function boundary**: internal fns → Yul functions,
  internal calls → Yul calls, modifiers → caller/callee. done-rel: `OpenWorld` +
  return values + control outcome, by induction on source fuel. **LARGE, HARDEST,
  and currently has no source IR to refine (D1).**
- **Sm — memory layout**: structural values/`bytes` → flat Yul memory + FMP +
  head/tail. done-rel: value ≅ memory region under an invariant; final
  `memory`/`activeWords` match. LARGE — full translation layer (our memory is an
  object heap; the would-be byte model is dead).
- **Sx — ABI codec**: encode/decode/dispatch → byte/memory ops. done-rel:
  byte-identical bytes. MEDIUM, rides on Sm.
- **Sy — storage layout**: typed paths/mappings/arrays/packing → slot arithmetic
  via keccak (the materialized `E`). done-rel: typed store ≅ word store under `E`
  = `OpenWorld` storage. SMALL–MEDIUM, near-identity on our side.
- **Sk — arithmetic/control**: checked ops+Panic → Yul overflow snippets;
  structured control → Yul control. done-rel: word equality + control match.
  SMALLEST, near-1:1.
The transcript is the shared `Query` alphabet at every seam; fuel exhaustion is
the reflectable `outOfFuel` outcome each `trans` `hReflect` needs.

**Which tower layers are already cheap vs face a full translation layer.** The
earlier "well-positioned" framing was too flat — position varies sharply *by
layer*:
- **Cheap / already at the Yul level (aligned representation):** *Sy (storage)* —
  storage is word-addressed, solc-exact, real keccak; *Sk (arithmetic/control)* —
  word ops definitionally `EvmYul.UInt256`, checked = wrapping-builtin + explicit
  Panic = solc's own Yul shape, structured control lines up. Deterministic
  Yul-compatible evaluation order and the `outOfFuel` outcome make the shared
  parts of *every* seam (transcript, truncation) well-defined. These are the
  expensive-to-get-right primitives, and they are right.
- **Full translation layer (representation mismatch):** *Sm (memory)* — the
  object-heap memory has no correspondence to Yul's flat bytes and the would-be
  byte model is dead code (a new model, invariant, and per-type layout proofs);
  *Sx (ABI)* rides on it. *Sd (dispatch)* is a moderate structural map.
- **Broken source (no IR to refine):** *Sc (calling convention)* — the function
  boundary is inlined away and recursion is unrepresentable before the core
  exists. This is the tower's structural break, not a wart.

So the current core is a strong **Sy/Sk/Sd** anchor, an adequate-but-mismatched
**Sm/Sx** anchor, and a **broken Sc** anchor — mid-tower, with layers collapsed
and one prematurely destroyed, not the top of a single short hop.

**Top 3–5 "do it now" refactorings:**
1. **N1** — delete the ~14 dead observation-era classifier enums (second, smaller
   observation-layer; zero uses; skill+roadmap both say delete).
2. **N2** — retire/mark the dead byte-memory shadow in `Runtime` (unwired, and
   actively misleading to the future memory-refinement layer).
3. **N3** — move in-file example defs to `Witness/` (no mixed-concern file).
4. **N4** — fix `Ast.lean`'s import of `ABI.lean` (surface AST should not depend
   on the interpreter; keeps the core-first dependency floor clean).
5. **D1 (record, don't build)** — the inlined-function-boundary /
   unrepresentable-recursion mismatch destroys the source IR for the tower's
   hardest layer (Sc, calling convention); record it as the #1 lowering-design
   question **and** a candidate recorded semantic gap (recursion/deep-call-graph
   silent rejection). **P1** (materialize the storage-layout `E`, the Sy artifact)
   as optional early de-risking, lean toward deferring.

Everything genuinely lowering-shaped (memory layout, revert-bytes relation, exp,
immutables, gas/initCode alignment, elaboration correctness) is deferred, per the
roadmap's "no new speculative interfaces" — the current phase only needs to leave
the source semantics clean, and it is close.

*Deliverable written (uncommitted) at `docs/compile-to-yul-readiness.md`.*
