# Implementation-level solc-vs-Solidus divergence review (round 2)

**Second implementation-level pass.** The first pass
(`docs/solc-implementation-divergences.md`, commit `0e29538`) read the
arithmetic / cleanup / conversion / ABI-**decode** / storage-helper families at
the emitted-Yul level and found them faithful, then listed the families it did
**not** reach. This round covers exactly those unreached families:

1. `ExpressionCompiler.cpp` LValue / compound-assignment / tuple-assignment /
   `delete`-per-type / evaluation-order micro-rules.
2. ABI **encode** side (`ABIFunctions.cpp` head/tail for nested dynamics) +
   `abiEncodePacked` / packed widths.
3. Analysis passes — full bodies: `ViewPureChecker.cpp`, `OverrideChecker.cpp`,
   `ControlFlowAnalyzer` (+ `ControlFlowGraph`/`ControlFlowRevertPruner`),
   `ContractLevelChecker.cpp`, `PostTypeChecker.cpp`, `ImmutableValidator.cpp`.
4. Memory management — memory `delete`/default init and the memory/storage clear
   families in `YulUtilFunctions`/`LValue`.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `0a57a7f`. Read-only: nothing
built or run. Findings are **CONFIRMED** (both sides read to the rule) or
**INFERRED** (deduced, wants a probe).

---

## Executive summary

**Families / passes actually read (code, not tests), both sides:**

- `ViewPureChecker.cpp` (whole body) ↔ Solidus `TypeCheck.lean`
  `mutabilityAllows*` / `requireState*Allowed` and every read/write/call/member
  site.
- `OverrideChecker.cpp` (whole body) ↔ Solidus `TypeCheck.lean` override section
  (`OverrideMember`, `overrideVisibilityAllowed`, `overrideMutabilityAllowed`,
  `checkOverridable`, `checkCompatible`, `checkOverrideSpecifier`).
- `ControlFlowAnalyzer.cpp` (+ graph/revert-pruner) ↔ Solidus pointer
  definite-assignment flow (`checkPointerReturnDefiniteAssignment`,
  `checkLocalPointerDefiniteAssignment`, `uninitializedStorageReturnTarget`).
- `ExpressionCompiler.cpp` assignment/compound/inc-dec/tuple + `LValue.cpp`
  `setToZero` + `CompilerUtils::pushZeroValue` ↔ Solidus `assignExpr` /
  `assignOpExpr` / `applyIncDec` / `assignTuple` / `deleteStorage*` /
  `Value.defaultLike`.
- `ABIFunctions.cpp` `tupleEncoder` / `abiEncodingFunctionSimpleArray` /
  `abiEncodingFunctionStruct` / `tupleEncoderPacked` / `leftAlignFunction` ↔
  Solidus `ABI.lean` `encodeValues*` / `encodeDynamicPayload?` and
  `Interpreter.lean` `abiEncodePacked*`.
- `ImmutableValidator.cpp`, `ContractLevelChecker.cpp`, `PostTypeChecker.cpp`
  (headline rules) ↔ Solidus `TypeCheck.lean`.

**Headline: NO new wrong-VALUE / wrong-ORDER soundness divergence** was found in
the ABI-encode, expression-compiler eval-order, `delete`-per-type, or
memory-default families — each was read to the rule on both sides and computes
the same bytes / same result / same order. This is an earned negative for the
value-producing code paths.

The NEW findings are **acceptance-boundary** divergences in the analysis passes.
The single most contest-relevant is an **over-accept** (Solidus accepts a
program solc rejects), ranked first:

**Ranked NEW findings**

| # | Area | Direction | Severity | Confidence |
|---|------|-----------|----------|------------|
| **E1** | view/pure: non-rational immutable read in `pure` | **over-accept** (Solidus runs, solc errors 2527) | over-accept — contest-relevant wrong-accept | CONFIRMED |
| E2 | view/pure: `this.f.selector` in `pure`/non-view | over-reject | COMPLETENESS | CONFIRMED |
| O1 | override: duplicate contract in `override(A,A)` | over-accept | COMPLETENESS (harmless) | CONFIRMED |
| CF1 | control-flow: inline-asm in storage/calldata-ptr-return fn | over-reject | COMPLETENESS | CONFIRMED |
| CF2 | control-flow: no revert-pruning of always-reverting callees | over-reject | COMPLETENESS | **FIXED 2026-07-08** (DECISIONS.md; always-reverts fixpoint, lane `cf2-revert-pruning`) |
| CF3 | control-flow: fuel/placeholder conservative fallback | over-reject | COMPLETENESS | INFERRED |
| PT1 | post-type: `constant` cyclic-dependency not detected | over-accept | COMPLETENESS | INFERRED |
| AE1 | encode-packed: `bytes[]`/`string[]` element in `abi.encodePacked` | over-accept / wrong-bytes if unguarded | COMPLETENESS/validation | INFERRED |

**E1 is the only finding with a live differential edge that a solc-vs-Solidus
harness would hit on a small, natural program** (a `pure` function returning a
`keccak256`-initialized immutable). Everything else is a niche over-reject, a
harmless over-accept, or wants a probe.

---

## 1. Expression-compiler / evaluation-order / `delete` — FAITHFUL (no new soundness)

Read `ExpressionCompiler.cpp` assignment/compound/inc-dec/tuple, `LValue.cpp`
`GenericStorageItem::setToZero` / `MemoryItem::setToZero`, and
`CompilerUtils::pushZeroValue`, against Solidus `Interpreter.lean`.

| Rule | solc file:line | Solidus | Verdict |
|---|---|---|---|
| `a = b` / `a[i]=v`: RHS evaluated **before** LHS-lvalue (so **value before index**) | `ExpressionCompiler.cpp:319` (rhs), `:331` (lhs setup) | `assignExpr` under `ChildEvalOrder.rightToLeft` `Interpreter.lean:6051-6058`, default `:6796-6800` | FAITHFUL (CONFIRMED) |
| Compound `a op= b`: LValue set up once, read once, written once; value types only | `:339-370` (`retrieveValue :348`, `storeValue :370`) | `assignOpExpr :6061-6084` / `assignOpCleanupExpr :6085-6116` (`resolveLValue`→`read`→`write`, each once) | FAITHFUL (CONFIRMED) |
| `<<=`/`>>=` clean amount **unchecked** even inside a checked block | `:351` `appendShiftOperatorCode` | `:6110-6114` | FAITHFUL (CONFIRMED) |
| Prefix result = new value; postfix result = old value; LValue read once | `:484-521` (`DUP1` old at `:489`) | `applyIncDec`/`applyIncDecCleanup :5742-5766` (`returnOld`) | FAITHFUL (CONFIRMED) |
| `delete` value type → packed-aware zero | `LValue.cpp:485-511` | scalar/packedScalar default `Interpreter.lean:3577-3585,3862-3869` | FAITHFUL |
| `delete` dynamic storage array → clear elems + length 0 | `LValue.cpp` `clearArray` | `:3606-3621` | FAITHFUL |
| `delete` storage struct → recursive, **skips mapping members** | `LValue.cpp:474-475` (`continue` on mapping) | struct case; `StorageLayout.mapping _ _ => ok` no-op `:3622-3623` | FAITHFUL |
| `delete` whole mapping → no-op | (skipped) | `deleteStorageField :3860-3861` | FAITHFUL |
| `delete` `bytes`/`string` → length 0 | | `:3602-3605,3840-3849` | FAITHFUL |
| `delete` memory dyn array → length-0 pointer; fixed array/struct → freshly zeroed, same length / all fields | `CompilerUtils.cpp:1370-1404` | `Value.defaultLike :226-228` | FAITHFUL |
| `(a,b)=(b,a)`: whole RHS tuple → values first, then write targets | `ExpressionCompiler.cpp:309-335` | `Stmt.assignTuple :7718-7725` | FAITHFUL (correct swap) |

**Note (unspecified order, not a divergence):** for `a[i][j]=v` with
side-effecting `i`,`j`, legacy `ExpressionCompiler` walks base-before-index
(`IndexAccess :2219`) → order `v,i,j`; Solidus `resolveLValue` for `Expr.index`
walks index-before-base (`:6747-6754`) → `v,j,i`. Solidity leaves a node's child
evaluation order **unspecified**, and Solidus models this explicitly
(`ChildEvalOrder.unspecifiedOrders :6802-6807`). Not a wrong-value divergence for
conformant programs. OUT-OF-SCOPE.

**IN-FLIGHT (not re-examined):** R1 nested-tuple-LHS-with-internal-call-RHS, R2 /
G14 storage-array copy (`copyArrayToStorage` interaction) — untouched here.

---

## 2. ABI **encode** side — FAITHFUL (no wrong-byte divergence)

Read `ABIFunctions.cpp` `tupleEncoder`, `abiEncodingFunctionSimpleArray`,
`abiEncodingFunctionStruct`, `tupleEncoderPacked`, `leftAlignFunction` against
Solidus `ABI.lean` `encodeValues*`/`encodeDynamicPayload?` and
`Interpreter.lean` `abiEncodePacked*`.

**Non-packed head/tail nesting — CORRECT (CONFIRMED both sides).** solc's base
rule is `mstore(add(headStart,<pos>), sub(tail,headStart))`
(`ABIFunctions.cpp:91`) with `headStart` advanced past the head area
(`:72,77`); for arrays `headStart := pos` is set **after** the length word
(`abiEncodingFunctionSimpleArray :558-564`), so element offsets exclude the
length slot; struct members get one head word each with the dynamic member's head
= offset from the struct head start (`:942-955`). Solidus mirrors all three:
top-level tuple `encodeValues?`/`encodeValuesAux? ABI.lean:292-317` (offset from
arg-data start), dynamic array `encodeDynamicPayload? :210-238`
(`initialOffset := wordBytes*len*elementWords`, result `length ++ heads ++ tails`
so offsets are measured post-length), fixed-array-of-dynamic `:239-256`, and
tuple/struct-with-dynamic-member `:257-289`
(`initialOffset := wordBytes*listAbiHeadWords?`).

Worked example `uint[][] = [[1],[2,3]]`: both sides emit
`0x20, 2, 0x40, 0x80, 1,1, 2,2,3` word-for-word. Head-area sizing agrees
(`headSize`/`calldataHeadSize` ↔ `Ty.staticAbiHeadWords?`/`listAbiHeadWords?`
`ABI.lean:96-137`).

**Packed widths — CORRECT; W1 already landed.** Solidus's packed encoder is
`Interpreter.lean` `abiEncodePackedValues? :4978-4989` /
`abiEncodePackedValue? :4916-4944` with per-arg narrow widths
`Ty.packedTopWidth Interface.lean:3262-3273`. Verified vs solc packed rules:
narrow `uintN`/`intN` → N/8 low bytes incl. two's-complement, `enum` → 1,
`address` → 20, `bool` → 1, `bytesN` → N, `uint256`/`int256` → 32, dynamic
`bytes`/`string` top-level → raw bytes with **no** length and **no** padding, and
**array elements padded to 32 even in packed mode**
(`abiEncodePackedArrayElement? :4946-4952`). The prior-flagged **W1** narrow-int
packed width reads as **FIXED**, not in-flight; not re-reported as new.

**AE1 (INFERRED, minor):** `abiEncodePackedArrayElement? :4946-4952` rejects
`fixedArray`/`dynamicArray`/`tuple` element types but a `bytesCalldata` element
falls through to right-pad-to-32 without a length prefix. solc rejects
arrays-of-dynamic in `abi.encodePacked` at type-check. **If** Solidus's
`TypeCheck` predicate (`badAbiEncodePackedNestedArray`, ~`TypeCheck.lean:23336`)
does not also reject a `bytes[]`/`string[]` argument, this path emits bytes solc
never emits. This is a validation/over-accept edge, not a wrong-value on an
accepted-by-both program. Wants a probe of the full encodePacked validation
predicate.

---

## 3. Analysis passes

### 3a. `ViewPureChecker.cpp` — one over-accept (E1) + one over-reject (E2)

solc is a whole-AST visitor: each node calls `reportMutability(m,loc)` which
lattice-joins (`Pure<View<NonPayable<Payable`) into
`m_bestMutabilityAndLocation` and errors when `m` exceeds the declared
mutability (`ViewPureChecker.cpp:233-305`). Solidus threads
`env.currentMutability` and calls `requireState{Read,Write}Allowed` /
`requireLogOrCreateAllowed` / `requireCallMutabilityAllowed`
(`TypeCheck.lean:1703-1781`) at each site.

The rule correspondence is otherwise **complete and CONFIRMED** — see the table
at the end of this section. The two divergences:

#### E1 — non-rational immutable read in a `pure` function — over-accept — SOUNDNESS-adjacent (contest-relevant wrong-accept) — CONFIRMED

- **solc** `ViewPureChecker.cpp:194-199`: an immutable read is `Pure` **only if**
  `varDecl->value() && value()->annotation().type->category() ==
  Type::Category::RationalNumber` (pure literal/rational arithmetic). For **any
  other** initializer the immutable read is `View`. So a `pure` function reading
  such an immutable is TypeError **2527**.
- **Solidus** `TypeCheck.lean:8250-8269`: `hasCompileTimeImmutableInit` /
  `runtimeStateNameWith?` drop from `stateNames` **any** immutable whose init
  satisfies `exprIsCompileTimeConstant` (`:8119-8173`). That predicate is far
  broader than solc's `RationalNumber`: it is true for a reference to a
  `constant` (`:8122`), for `keccak256`/`sha256`/`ripemd160`/`ecrecover`/
  `addmod`/`mulmod`/`erc7201` (`:8083-8086`), `abi.encode*`/`decode`
  (`:8088-8091`), `bytes`/`string.concat`, and `type(T).wrap`/`unwrap`
  (`:8093-8114`). Wired at `:12157-12159`
  (`stateNames := runtimeStateNamesWith ... stateVars`). The ident-read at
  `:5115-5140` gates `requireStateReadAllowed` on
  `isState := env.isStateName name` (`:5118,5130`), which reads `stateNames`.
- **Consequence:** for e.g. `bytes32 immutable H = keccak256("x");` (or
  `uint constant A = 5; uint immutable B = A;`), `H`/`B` is not in `stateNames`,
  so `isState=false`, so the read skips `requireStateReadAllowed`. A
  `function f() public pure returns (bytes32) { return H; }` is **accepted by
  Solidus, rejected by solc (2527)**. The runtime **value** is identical (both
  compute `keccak256("x")`), so this is purely an acceptance divergence — but it
  is the wrong-accept direction (Solidus runs a program solc refuses to
  compile), which a differential harness flags. This is the top NEW finding.

#### E2 — `this.f.selector` in `pure`/non-view — over-reject — COMPLETENESS — CONFIRMED

- **solc** `ViewPureChecker.cpp:357-370`: `visit(MemberAccess)` special-cases
  `this.f.selector`, returns `false`, so the `this` identifier is never visited
  and contributes **no** mutability — the expression stays `Pure`.
- **Solidus** `TypeCheck.lean:5188-5221`: the `.selector` case unconditionally
  `checkExpr env base` on the inner `this.f`, recursing into `Expr.ident "this"`
  at `:5105-5106` which runs `requireStateReadAllowed`. In a `pure` function this
  fails.
- **Consequence:** `function g() external pure returns (bytes4) { return
  this.f.selector; }` is **rejected by Solidus, accepted by solc**.

**ViewPureChecker rule table (all CONFIRMED SUPPORTED unless noted):** state-var
read→View / write→NonPayable (`:200-201` ↔ `:5130-5131` read, `:6980,7142,7668,
7760` write); `this` reads address→View (`:208-211` ↔ `:5105-5106`); `msg.value`
→Payable-only-in-payable-public/ctor (`:404-414,270-294` ↔ `:5286-5304`,
**IN-FLIGHT G2**); `msg.data`/`msg.sig` pure, other `msg.*`→View (`:388-412` ↔
`:5280-5286`); `block.*`/`tx.*`→View (`:411-412` ↔ `:5322,5341`);
`<addr>.balance`/`.code`/`.codehash`→View (`:382-383` ↔ `:5473-5503`); storage
member/index/`.length`→View/NonPayable (`:417-459` ↔ `stateLValue :5451,5545`);
call joins callee mutability, payable-callee needs only NonPayable (`:326-355` ↔
`mutabilityAllowsCall :1718-1727` + sites `:5733-6772`); `selfdestruct`→NonPayable
(`:4417`); `.transfer/.send/.call/.delegatecall`→NonPayable, `.staticcall`→View
(`callMemberMutability? :1751-1759`); emit/`new`→NonPayable (`:9010`, `:6458`);
`gasleft`/`blockhash`/`blobhash`→View (`:1770-1775,4331-4339`); modifier body
mutability propagated (`:462-471` ↔ `checkBodyForCaller :10312-10349`).

**Non-divergence:** solc analyzes each Yul opcode's mutability so a `pure`/`view`
function may contain pure/view inline assembly (`AssemblyViewPureChecker
:38-125,225-231`); Solidus rejects **all** inline assembly
(`TypeCheck.lean:9031-9032`). This is a broad unsupported-feature over-reject, not
mutability-specific — OUT-OF-SCOPE. solc's `now`→View (`:213-216`) is dead in
0.8.35 — OUT-OF-SCOPE.

### 3b. `OverrideChecker.cpp` — one harmless over-accept (O1)

Solidus's override checker is a near-complete reimplementation. Every substantive
acceptance rule is enforced (CONFIRMED), often via a differently-worded error:
missing-`override` (9456 ↔ `checkOverrideUse TypeCheck.lean:9647-9649`,
interface-implicit-virtual `:9505-9506`); override-non-virtual (4334 ↔
`checkOverridable :9415-9421`); cannot-override-public-state-var (1452 ↔
state-var members `virtual:=false :9473`); visibility change external→public only
(9098 ↔ `overrideVisibilityAllowed :9329-9335`); public-var-overrides-external-fn
(5225 ↔ `:9438,9471`); mutability direction (6959 ↔ `overrideMutabilityAllowed
:9337-9350`, matched against enum order `Pure<View<NonPayable<Payable`
ASTEnums.h:37); return-type match (4822 ↔ `:9427-9428`); param/return data
location unless public-overriding-external (7723/1443 ↔ `:9429-9437`);
implemented-with-unimplemented (4593 ↔ `:9681-9684`); modifier-override signature
(1078 ↔ `:9870-9879`); `override(...)` names-a-non-base (2353 ↔
`checkOverrideSpecifier :9632-9641`); `override(...)` missing-contracts-when->1
(4327 ↔ `:9634-9641`); overrides-nothing (7792 ↔ `:9675-9677,9705-9708`);
cross-namespace clashes (5631/1469/1456 ↔ `checkNoInheritedNamedDeclarationClashes
:12316-12325,12268-12274`).

#### O1 — duplicate contract in `override(A, A)` — over-accept — COMPLETENESS — CONFIRMED

- **solc** `OverrideChecker.cpp:850-879` `checkOverrideList` rejects a duplicate
  contract in the override list (4520_error).
- **Solidus** `TypeCheck.lean:9639` `checkOverrideSpecifier` uses `pathSetsEqual`
  (membership both directions), which ignores duplicates — `override(A, A)` is
  accepted. Harmless over-accept.

**PARTIAL / IN-FLIGHT:** ambiguous unrelated-base override (solc 6480,
`OverrideChecker.cpp:725-822`, biconnected/cut-vertex algorithm) is approximated
by Solidus `checkInheritedConflicts`/`hasConflictFor` with an
`originStrictlyInherits` dominance test (`:9714-9758`, wired `:12331-12334`);
diamond corner cases may diverge — this belongs to the in-flight **G6** arc, not
re-reported in detail.

### 3c. `ControlFlowAnalyzer` — the one hard error is enforced; three niche over-rejects

**Key fact (clears a suspected over-accept):** solc's `ControlFlowAnalyzer`
emits exactly **one error** (3464) and **two warnings** (5740 unreachable-code,
6321 unnamed-return-may-be-unassigned). Value-type locals are default-initialized,
so solc does **not** require definite assignment for them and does **not** error
on a missing `return`. Therefore Solidus's "read the default value" behavior for
a possibly-unassigned local / missing return is **not** an over-accept — solc
accepts those same programs (both just run with the default). CONFIRMED
non-divergent.

- **Uninitialized storage/calldata pointer access-or-return** (3464,
  `ControlFlowAnalyzer.cpp:160-174`) → **SUPPORTED as a hard error**. Solidus has
  a real definite-assignment flow: return pointers
  `checkPointerReturnDefiniteAssignment TypeCheck.lean:10907-10925` (wired
  `:11389`), local pointers `checkLocalPointerDefiniteAssignment :11290+` (wired
  `:11388`, modifiers `:11428`); interpreter kept consistent by
  `uninitializedStorageReturnTarget Interpreter.lean:7011` (bound
  `:7160-7162`, miss → panic `Interface.lean:8148`). CONFIRMED.
- Unreachable code (5740, warning) and unnamed-return-unassigned / missing-return
  (6321, warning) → solc only **warns and compiles**; Solidus accepts too. Not
  acceptance divergences (warning-parity only, UNTESTED).

The three Solidus-only over-rejects (all COMPLETENESS, all sound-preserving):

- **CF1 (CONFIRMED)** — `Stmt.inlineAssembly` unconditionally sets
  `unsafeReturn := true` (`TypeCheck.lean:10831-10832`), so **any** function with
  a storage/calldata return pointer **and** any inline-assembly block is
  rejected, even when the pointer is properly assigned and the assembly never
  touches it. solc analyzes the actual CFG assignment.
- **CF2 (INFERRED)** — solc runs `ControlFlowRevertPruner` to prune paths through
  always-reverting callees before the uninitialized-access check; Solidus prunes
  only builtin terminals (`revert`/`selfdestruct` `isTerminalBuiltinCall
  :10682-10687`, `revertCall :10812-10815`, `return :10816-10823`). A pointer
  read reachable only after an always-reverting **helper call** would be flagged
  by Solidus but accepted by solc.
- **CF3 (INFERRED, effectively unreachable)** — fuel exhaustion
  (`defaultPointerReturnFlowFuel = 4096 :10905`) and a `modifierPlaceholder` with
  no continuation (`:10839`) both fall back to `unsafeReturn := true` —
  over-reject only for pathologically deep bodies / malformed modifier expansion.

### 3d. `ContractLevelChecker` / `PostTypeChecker` / `ImmutableValidator`

- **ImmutableValidator** (`ImmutableValidator.cpp:45-68`) enforces only "cannot
  write to an immutable outside inline-init or the constructor" (1581). Solidus
  matches: an immutable ident is an lvalue only when `env.inConstructor`
  (`TypeCheck.lean:5138`, `:4163`). SUPPORTED. (The "every immutable must be
  assigned exactly once" invariant is a codegen assertion in solc — "Leftover
  immutables." — with no isolated analysis-pass error string; not independently
  confirmable read-only, left as a probe in §5.)
- **ContractLevelChecker** structural rules read: receive-function
  payable/external/no-return/no-params (`:211-227`), abstract-if-unimplemented
  (`:348-353`), library constraints (`:525-561`), too-much-storage
  (`:601-603`). Solidus models abstract-implemented
  (`OverrideMembers.checkInheritedAbstractImplementedAux TypeCheck.lean:9760`)
  and `contractCanReceiveEther` (`:1226-1237`); the full receive-signature and
  storage-size rules were not exhaustively cross-checked (candidate for §5).
- **PostTypeChecker**: `ConstStateVarCircularReferenceChecker`
  (`PostTypeChecker.cpp:154-245`, 6161) rejects a `constant` with a cyclic
  dependency (`uint constant A = B; uint constant B = A;`). Solidus models
  **struct** reference cycles (`Ty.hasForbiddenStructReferenceCycle
  TypeCheck.lean:11508+`) but I found **no** constant-value cycle detector →

#### PT1 — `constant` cyclic dependency not detected — over-accept — COMPLETENESS — INFERRED

Solidus appears to lack solc's `ConstStateVarCircularReferenceChecker`. A
self/mutually-cyclic `constant` that solc rejects (6161) would either be
over-accepted or fail during Solidus's fuel-bounded constant folding — the exact
observable wants a probe. INFERRED, low priority.

---

## 4. Memory management — FAITHFUL

The memory-relevant behaviors reachable through the reviewed families —
memory-`delete` default init (`Value.defaultLike Interpreter.lean:226-228`
matching `CompilerUtils::pushZeroValue :1333-1412`), memory dynamic-array →
length-0 pointer, fixed-array/struct → freshly zeroed same-shape — are FAITHFUL
(see §1). The nested-struct `abi.decode` into memory and free-memory-pointer
discipline were CONFIRMED faithful by the first pass at the observable level and
were not re-derived here (listed in §5 as still-not-reached at codegen level).

---

## 5. Families reviewed vs still-not-reached

**Reviewed this round (both sides, verdict as noted):**

- [x] ExpressionCompiler assignment/compound eval-order (value-before-index) — FAITHFUL
- [x] Compound-assign reads-lvalue-once, `<<=`/`>>=` unchecked cleanup — FAITHFUL
- [x] Prefix/postfix inc-dec result timing — FAITHFUL
- [x] `delete` per type: value, dyn array, struct(skip mapping), mapping, bytes/string, memory array/fixed/struct, storage pointer — FAITHFUL
- [x] Tuple/swap assignment order (`(a,b)=(b,a)`) — FAITHFUL
- [x] ABI **encode** nested head/tail: `T[][]`, `string[]`, struct-with-dynamic, static-then-dynamic tuple — FAITHFUL
- [x] `abi.encodePacked` widths + array-element-padded-to-32; packed dynamic bytes/string — FAITHFUL (W1 landed); AE1 edge INFERRED
- [x] `ViewPureChecker` full body — E1 over-accept, E2 over-reject, rest SUPPORTED
- [x] `OverrideChecker` full body — O1 over-accept; rest SUPPORTED; ambiguous-base IN-FLIGHT (G6)
- [x] `ControlFlowAnalyzer` (+ graph, revert-pruner) — 3464 enforced; CF1/CF2/CF3 over-rejects; warnings non-divergent
- [x] `ImmutableValidator` write-location rule — SUPPORTED
- [x] `PostTypeChecker` const-cycle (PT1 INFERRED), override-specifier-is-contract, var-in-interface (headline)
- [x] `ContractLevelChecker` headline rules (abstract, receive, library, storage-size) — partially cross-checked

**Still NOT reached (worklist for a future pass):**

- `ContractLevelChecker` receive/fallback **signature** rules and duplicate/
  base-constructor-argument checks — cross-check Solidus at codegen/accept level.
- Immutable "assigned **exactly once** on every constructor path" — solc enforces
  via codegen invariant ("Leftover immutables."); confirm whether Solidus rejects
  a never-initialized / doubly-initialized immutable or reads a default (probe).
- `abi.encodePacked` full **validation** predicate
  (`badAbiEncodePackedNestedArray` and siblings) — resolve AE1: does Solidus
  reject `bytes[]`/`string[]`/struct arguments the way solc does?
- `abiDecodingFunctionStruct` nested-struct decode into memory + free-memory-
  pointer discipline at the **codegen** (Yul) level — first pass confirmed the
  observable, not the emitted allocation sequence.
- `DeclarationTypeChecker.cpp` (type resolution / data-location defaulting) —
  not opened this round.
- solc's `ControlFlowRevertPruner` full algorithm vs Solidus terminal-pruning
  (CF2) — a probe would confirm/deny the over-reject on a concrete shape.

---

## 6. Bottom line

Reading solc's real code paths for the previously-unreached families — the
expression-compiler LValue/compound/`delete`/tuple eval-order rules, the ABI
**encode** head/tail and packed widths, memory-default init, and the full
analysis-pass bodies (`ViewPureChecker`, `OverrideChecker`,
`ControlFlowAnalyzer`, and the contract/post-type/immutable checkers) — surfaced
**no new wrong-value or wrong-order soundness divergence**. Every value-producing
path (encode bytes, `delete` results, inc/dec/compound results, tuple swap) was
read to the rule on both sides and matches.

The NEW divergences are all at the **acceptance boundary**. The one with a live
differential edge is **E1**: Solidus treats an immutable initialized by
`keccak256`/`abi.*`/a `constant` reference as a compile-time constant and lets a
`pure` function read it, whereas solc classifies that read as `View` and rejects
the function (2527) — an over-accept on a small, natural program. The remainder
are a harmless override over-accept (O1), a not-modeled constant-cycle check
(PT1), three sound-preserving control-flow over-rejects (CF1–CF3), and one
encode-packed validation edge (AE1). The suspected control-flow over-accept
(reading a default for possibly-unassigned locals / missing return) was
**cleared**: solc only warns there, so both accept.
