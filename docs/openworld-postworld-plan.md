# Open-World postWorld Plan: Full Arbitrary-Environment External Calls

Status: design, queued. Implementation begins only after the two in-flight arcs merge
(function-boundary refactor; A2 balance / A3 gasleft). Written 2026-07-06.

Decision of record: the user has chosen the **arbitrary-changes model** — on an external
call/create, the environment's answer may make arbitrary changes to the calling
contract's own account (storage words, transient storage, balance, nonce) and the
semantics adopts them on resume. This supersedes the Phase 5 "fail-closed
attributable-only re-projection" policy recorded in `docs/DECISIONS.md:310-319`.

Orchestrator ruling incorporated (2026-07-06):

1. **No representation change.** `State.storage : WordMap` is already slot-addressed
   words. Adoption is ordinary writes into that existing map (and the transient map,
   and the A2 `State.selfBalance`), keyed by slot. No separate "raw word storage"
   layer is introduced anywhere in this plan.
2. **Typed reads of non-canonical words are TOTAL and solc-faithful** (option a), not
   a layout-respecting environment restriction (option b). Rationale of record:
   (i) the Yul side's open-world theorems quantify over arbitrary answers and the
   forward relation resumes both sides on *identical* answers
   (`evm-compiler/EvmCompiler/Simulation/Interaction.lean:1393-1405`,
   `Rel.request : ∀ answer, …`); lowered Yul is defined on any word (cleanup/validation
   on read), so a fail-closed source would break the relation exactly where Yul
   computes, forcing an environment hypothesis through every composed theorem;
   (ii) "what deployed code observably does" is the fidelity standard used everywhere
   else in this repo; (iii) the per-type cleanup machinery largely exists;
   (iv) real reentrancy only writes canonical encodings, so totality serves the
   theorem's quantifier, not the fixtures. The "layout-respecting environment" class
   may reappear later as a *theorem-side refinement* (a hypothesis some downstream
   lemma adds to say more), never as semantics-side fail-closure.

---

## 1. The target, precisely (what Yul does today)

All citations into the read-only reference `/Users/dan/Projects/evm-compiler`.

### 1.1 Shape of the boundary

- Query alphabet: `Query = resource ResourceQuery | external OpenWorld ExternalRequest`
  (`EvmCompiler/Simulation/Interaction.lean:656-658`). The **outgoing world snapshot is
  part of the query itself**.
- `OpenWorld` (`EvmCompiler/Simulation/OpenWorld.lean:255-259`):
  `accounts : EvmYul.AddrMap OpenAccount`, `substate : EvmYul.Substate`,
  `createdAccounts : RBSet OpenAddress`.
- `OpenAccount` (`OpenWorld.lean:16-22`): `nonce`, `balance`, `storage : EvmYul.Storage`,
  **`transientStorage : EvmYul.Storage`** (yes — transient is carried; a reentrant
  callee running our code can change our transient storage and the model expresses it),
  `codeBytes : ByteArray` (code deliberately bytes-only, no AST).
- `Substate` (`evmyul EvmYul/State/Substate.lean:49-56`): selfdestruct set, touched
  accounts, refund, accessed accounts, accessed storage keys, **`logSeries`**.
- Requests: `CallRequest` (`Interaction.lean:174-183`) = kind, requestedGas, caller,
  recipient, codeAddress, transferValue, apparentValue, calldata bytes, permission;
  `CreateRequest` (`:191-197`) = kind, creator, value, initCode bytes, salt?, permission.
- Responses: `CallResponse` (`:660-664`) = success, returnData, **postWorld**,
  returnedGas; `CreateResponse` (`:676-680`) = address, returnData, **postWorld**,
  returnedGas. `Query.defaultAnswer` (`:709-716`) fails the call and **echoes the
  query's own snapshot back as postWorld** — the canonical no-op answer.

### 1.2 Emit and adopt

`callEval` (`EvmCompiler/Yul/InteractionSemantics.lean:122-141`):

```
let world := Simulation.OpenWorld.ofYulShared state.sharedState
.request (.external world (.call request)) fun response =>
  let machine := callLocal.finishMachine … response.returnData
  .done (.ok (state.withWorldAndMachine response.postWorld machine, [response.statusWord]))
```

- **Outgoing**: `ofYulShared` (`OpenWorld.lean:479`, via `ofYulState :469-472`) snapshots
  the **entire account map** (all accounts, not just self), the full substate (including
  the caller's accumulated `logSeries`), and `createdAccounts`.
- **Adoption**: `withWorldAndMachine` (`InteractionSemantics.lean:85-89`) →
  `installYulShared` (`OpenWorld.lean:523-526`) → `installYul` (`:505-510`):
  the answered `postWorld` **wholesale replaces** `accountMap`, `substate`, and
  `createdAccounts`. Only the protected frame survives from `base`: execution env,
  block/tx data, var store, machine state (docstring `:501-504`). Return data is
  applied to caller memory separately via `CallLocal.finishMachine`
  (`Interaction.lean:684-690`). `createEval` (`:143-162`) is identical, resuming on
  `response.address`.
- **Round-trip law**: `ofYulShared_installYulShared : ofYulShared (installYulShared
  base world) = world` (`OpenWorld.lean:575-578`). This is the algebraic heart of the
  design; our mirror must satisfy the same law.

### 1.3 Quantification — how "arbitrary" is enforced

- `Rel.request` (`Interaction.lean:1393-1405`): related computations expose the same
  query and remain related **for every answer** — `∀ answer, Rel … (left answer)
  (right answer)`. In the lockstep proof `callEval_rel_callStep`
  (`EvmCompiler/Yul/FunctionsInteractionPrimitive.lean:293-324`) the proof is
  `Rel.request; intro response` with `response : CallResponse` completely
  unconstrained; both sides install `response.postWorld`.
- Derived views: `AllDone` (`Interaction.lean:801-811`, "every possible answer at every
  request"), `Executes`/`Transcript`/`Follows` (`:734-750, :1110-1125`),
  `Strategy := (query : Query) → Answer query` + `interpret`/`Rel.interpret`
  (`:2529-2552`).
- **There is no well-formedness predicate on `postWorld` anywhere.** The environment
  may rewrite the caller's own storage, balance, nonce, transient storage, logs, even
  codeBytes. The only discipline is that source and target consume the *same* answer.
- **Logs**: `logSeries` lives inside `substate`, which travels in both directions and
  is **swapped wholesale** on adoption (`installYul_substate`, `OpenWorld.lean:593-595`).
  The callee's logs come back merged into `postWorld.substate.logSeries`; a hostile
  answer may equally drop or rewrite the caller's prior logs. Logs are *not*
  caller-local on the Yul side, and our mirror must not treat them as such.

### 1.4 Where we are today (the gap)

All citations into this repo, `SolidCore/Solidity/Interpreter.lean` unless noted.

- `emitLowLevelCall` (`:1813-1821`) emits `Query.external default (.call request)` —
  the snapshot is the **empty** `default : OpenWorld` ("Checkpoint-1: world snapshot is
  a placeholder", `:1812`). `emitContractCreation` (`:1900-1907`) same.
- `decodeCallResponse` (`:1804-1809`) consumes only `success`/`returnData`;
  "**`postWorld` is ignored at checkpoint 1**" (`:1803`). `decodeCreateResponse`
  (`:1886-1896`) consumes only `address`/`returnData`.
- `ScriptedResponder.answerCall?`/`answerCreate?` fill `postWorld := default`
  (`:1997`, `:2015`); section comment `:1958`. `contextAnswer` (`:1929-1931`) is
  `Query.defaultAnswer`. `SolI.runWith` (`:2028-2049`) pattern-matches
  `Query.external _ (…)` — wildcard on the snapshot — and is fail-closed on unmatched
  requests (`:2021-2023`).
- The interaction types are the shared vendored package
  `/Users/dan/Projects/evm-interaction` (Lake dep, `lakefile.lean:13`; hash-checked
  byte-identical to evm-compiler by `scripts/check_shared_interaction_hashes.py`),
  bridged by abbrevs in `SolidCore/Solidity/Interaction.lean:19-31`. **No new types are
  needed: `OpenWorld`, `OpenAccount`, `CallResponse.postWorld` are already in our
  dependency graph.** The gap is purely in what we put in and take out.

---

## 2. Target semantics for solid-core-spine

### 2.1 The outgoing snapshot: `snapshotWorld`

New pure function, `snapshotWorld (context : Context) (state : State) : OpenWorld`
(names indicative). It **materializes** — it does not restructure any state:

Self account (`context.self`), an `OpenAccount`:

| OpenAccount field | Source | Citation |
|---|---|---|
| `storage` | `State.storage : WordMap` entries, verbatim (slot ↦ word) | `Interpreter.lean:721-729` |
| `transientStorage` | `State.transient : WordMap` entries, verbatim | `:722` |
| `balance` | **`State.selfBalance`** (A2's dynamic balance — see §4.1) | balgas `Interpreter.lean:734` |
| `nonce` | new `State.selfNonce : Word := 0` (see §2.4) | — |
| `codeBytes` | `context.accountCodes` lookup of `context.self` (empty if absent) | `Interpreter.lean:1404-1427` |

Other accounts: one `OpenAccount` per address appearing in `context.accountBalances` /
`context.accountCodes` / `context.accountCodehashes` — balance and codeBytes from those
maps, storage/transient empty, nonce 0 — **overridden by the current adopted world view
if one exists** (§2.3). We never model other accounts' storage contents; that is the
environment's business, and the empty maps are honest ("we assert nothing"). This
mirrors the *shape* of `ofYulShared` (whole account map) at our fidelity level.

Substate:

| Substate field | Source |
|---|---|
| `logSeries` | the canonical log series (§2.5): adopted prefix ++ `State.logEntries` projection (`Interpreter.lean:703-707, 734-736`) |
| `selfDestructSet` | from `State.selfdestructs` addresses (`:721-729`) |
| `touchedAccounts`, `accessedAccounts`, `accessedStorageKeys`, `refundBalance` | `default` — we do not track access sets or refunds. Declared fidelity gap, same code-erasure spirit as the Yul side's exclusion of gas counters. Recorded, not hidden. |

`createdAccounts`: seeded from `context.createdInTransactionAccounts` (`:1423`),
thereafter carried in the adopted world view.

**Corpus-neutrality**: nothing anywhere inspects the outgoing snapshot. The fixture
matcher chain is `LowLevelCallResult.matches` (`:1376-1380`) →
`Request.matchesRequest` (`SolidCore/Solidity/Shared/Call.lean:57-65`) — kind, target,
calldata, value, gas only; `Result`/`CreationResult` (`Call.lean:69-71, 108-112`) have
no world fields; every `Query.external` match in `runWith` and the witnesses wildcards
the snapshot (`Interpreter.lean:2033, 2041`; `SolidCore/Witness/Phase5Demo.lean:69-72`).
So Stage 1 (below) is a transcript-content change with zero matcher impact.

### 2.2 Adoption on resume: `adoptWorld`

`decodeCallResponse`/`decodeCreateResponse` stop ignoring `postWorld`. On resume,
before anything else in the continuation:

`adoptWorld (postWorld : OpenWorld) (context) (state : State) : State`:

- **Self account** — look up `context.self` in `postWorld.accounts`:
  - `State.storage := postWorld self.storage` entries — **ordinary slot-keyed writes
    into the existing WordMap; the map's contents are replaced by the answered
    contents.** No representation change: same `WordMap`, same slot keys, same word
    values. (Wholesale replacement, not merge — mirrors `installYul`'s account-map
    replacement, and is required for the round-trip law: a slot the environment
    *cleared to zero* must read zero afterwards.)
  - `State.transient := postWorld self.transientStorage` entries, same discipline.
    (EIP-1153 reality: a reentrant callee executing our code mutates our transient
    storage; the Yul model carries it — `OpenAccount.transientStorage`,
    `OpenWorld.lean:20` — so must we.)
  - `State.selfBalance := postWorld self.balance` (lands exactly on A2's field, §4.1).
  - `State.selfNonce := postWorld self.nonce`.
  - Self absent from `postWorld.accounts` ⇒ account destroyed by the environment:
    adopt the empty account (all-zero storage/transient/balance/nonce). Total, no
    error — same as Yul, where `installYulAccounts` (`OpenWorld.lean:485-494`) simply
    maps whatever accounts the answer contains.
- **Other accounts + createdAccounts** — stored as the live world view (§2.3).
- **Substate** — the canonical log series becomes `postWorld.substate.logSeries`
  (§2.5); selfdestruct set adopted likewise.

The continuation then proceeds exactly as today: build the
`LowLevelCallResult`/`ContractCreationResult` from success/returnData/address,
`recordExternalInteraction`, hand back to the evaluator.

**Round-trip law to state and prove** (mirror of `ofYulShared_installYulShared`,
`OpenWorld.lean:575-578`):

```
snapshotWorld context (adoptWorld w context s) = w
```

up to the declared fidelity gaps (access sets, refund — which we normalize to
`default` in both directions, so the law holds on the carried fields; state it on a
`normalizeSubstate` quotient or as field-wise equations). This lemma is the proof that
adoption is faithful and is the Stage 2 gate.

### 2.3 Where the adopted environment facts live

After the first adoption, `Context.accountBalances/accountCodes/accountCodehashes`
are **stale seeds**: post-answer reads of other-address balances, code, codehash,
extcodesize must come from the adopted world, not the static Context maps.

Design: `State.envWorld? : Option OpenWorld := none` (or the decomposed equivalent —
an `AddrMap OpenAccount` plus adopted substate/createdAccounts; the packaging is a
convenience, the self-account fields of §2.2 remain the existing `State` fields and
are *not* duplicated inside it — keep self out of `envWorld?` or keep it as the
authoritative copy for snapshot reassembly, but pick ONE owner: the existing `State`
fields own self; `envWorld?` owns others + substate extras + createdAccounts).

- Env lookups (`EnvLookup.accountBalance`, code/codehash/size, and
  `createdInTransactionAccounts`-dependent behavior) consult `State.envWorld?` first,
  falling back to the Context seed maps when `none` (pre-first-call reads unchanged ⇒
  behavior-preserving until an adoption actually happens).
- `Context` fields that become **seed-only** after this lands: `accountBalances`
  (already seed-only for self under A2), `accountCodes`, `accountCodehashes`,
  `createdInTransactionAccounts`. Document in their doc comments; do not remove — they
  are the entry-time initialization, exactly as A2 re-bases `selfBalance` from
  `accountBalances` at entry (balgas `Interpreter.lean:7623-7629`).
- Block/tx env (`blockEnv`, `txEnv`, `sender`, `origin`, gas) remain protected-frame
  facts, never adopted — mirroring `installYul`'s preservation of the execution
  environment (`OpenWorld.lean:501-504`).

### 2.4 Self nonce

We currently have no self-nonce anywhere (`State` `:721-729`, `Context` `:1404-1427`
carry none). Nothing in the interpreter reads it (create-address derivation is the
environment's business — our creates get their address from `CreateResponse.address`,
`:1886-1896`). We still carry it: `State.selfNonce : Word := 0`, snapshot it out, adopt
it back. Cost is one field; benefit is the round-trip law holds on all `OpenAccount`
fields and future `nonce`-observing features have the right home. Seeding from a new
optional `Context.selfNonce := 0` is acceptable; no fixture currently observes it.

### 2.5 Logs (the one structural mirror decision)

Yul: logs live in `substate.logSeries`, go out with the snapshot, and the answered
series **replaces** ours wholesale (§1.3). Our `State.events : List Event` is a typed,
interpreter-local record (`Stmt.emitEvent` `:7283-7290`, `Log.append` `:6334-6340`)
projected to shared entries by `State.logEntries` (`:734-736`); callee logs have no
representation today.

Design (minimal, no disturbance to typed assertions):

- Add `State.adoptedLogPrefix : List Log.Entry := []`. The **canonical log series** is
  `adoptedLogPrefix ++ state.logEntries-of-events-emitted-since-last-adoption`.
- Snapshot out: `substate.logSeries := canonical series`.
- Adopt: `adoptedLogPrefix := postWorld.substate.logSeries`; `events := []` (typed
  events emitted after resume append after the adopted prefix). With the echo default
  (§3.1) this composes to exactly today's series, so it is behavior-preserving until a
  responder actually appends callee logs.
- Existing witness/corpus assertions on `state.events` compare the typed list of
  *our* events; under echo answers, `adoptedLogPrefix ++ new events` projects to the
  same series but `state.events` itself is now only the post-last-call suffix. **This
  is the one place Stage 2 can break existing assertions** — see risk R1 for the
  audit obligation and the mitigation (assert on the canonical series, or keep
  `events` cumulative alongside the prefix by storing the split point instead of
  clearing; decide during Stage 2 implementation, favor whichever keeps all current
  fixtures green without edits).

### 2.6 Typed reads of arbitrary words — total, solc-faithful (Stage 0)

Ground truth established by compiling probes with
`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35 --ir` (IR retained at
`/tmp/solc-probes/Probe.yul`, `/tmp/solc-probes/EnumRead.yul`). The architectural
fact: solc's storage read pipeline is
`read_from_storage_split_* → extract (shr(offset*8, sload)) → cleanup_from_storage_t_X`,
and **`cleanup_from_storage_t_X` never reverts for any type** — it is pure
mask/signextend/shift. Validation and canonicalization happen at *use* sites via
`cleanup_t_X` (comparisons, conversions, ABI-encoding of returns).

Per-type table (w = raw word after the packed-lane right-shift):

| Type | solc read (`cleanup_from_storage`) | solc use (`cleanup_t`) | Observable on arbitrary w | Our current behavior | Divergence? |
|---|---|---|---|---|---|
| `bool` | `and(w, 0xff)` | `iszero(iszero(v))` | never reverts; slot=2 → truthy, getter returns 1 | reject w ∉ {0,1} → `typeMismatch` (`Interpreter.lean:378-380, 2118-2122`) | **YES — fail-closed read must become total** |
| enum (n members) | `and(w, 0xff)` | validator: `if iszero(lt(v,n)) Panic(0x21)` (verified `0x4e487b71…, 0x21`) | read unchecked; any use/compare/return of out-of-range → Panic 0x21 | packed extract unchecked at load; range enforced only at `enumFromUIntValue` (`:4855+`) with `enumConversion`, and ABI-side `AbiCleanup.enum` (`ABI.lean:85, 278`) | **YES — storage-read-then-use path must Panic 0x21 (semantics + revert-data), audit which use sites validate** |
| `uintN` (N<256) | `and(w, 2^N-1)` | same | mask, never reverts | packed bit-range extract (`wordBitRange` `:2394-2396`) — mask, OK | aligned (verify packed offsets only) |
| `uint256` | identity | identity | w | `some (Value.word w)` (`:381`) | aligned |
| `intN` (N<256) | `signextend((N/8)-1, w)` | same | sign-extend, never reverts | `intCast? (bytes*8)` with `none → typeMismatch` (`:2397-2399`) | **YES if `intCast?` is partial on any extracted range — make total signextend** |
| `int256` | identity | identity | w (two's complement) | `some (Value.int w)` (`:383`) | aligned |
| `address` / `address payable` / contract types | `and(w, 2^160-1)` | same | high 96 bits silently dropped, no revert, no code check | `some (Value.word w)` — **no mask** (`:381`) | **YES — mask to 160 bits on read** |
| `bytesN` | `shl(256-8N, w)` (left-align; storage keeps bytesN right-aligned in lane) | `and(v, leftmask)` | garbage below lane shifted out, never reverts | `some (Value.word w)` unshifted (`:384`) | **YES in principle — align our fixedBytes storage-word convention with the left-align read; audit our write-side convention first (if we store left-aligned already, read is identity+mask)** |
| `function() external` | `shl(64, w)` then split: addr = bits 32..191, selector = bits 0..31; bits ≥192 dropped, never reverts | — | total | `externalFunctionValueFromStorageWord` (`:133-137`): addr = w / 2^32 **without 160-bit truncation** | **YES (minor) — drop bits ≥192 of w (mask addr to 160 bits)** |
| `bytes32` | identity | identity | w | aligned | aligned |

Consequences:

- `Ty.storageValueFromWord?` (`:377-389`), `packedStorageValueFromWord?` (`:2373-2383`),
  `StorageField.storageValueFromWord?` (`:2639-2649`) become **total** on their
  supported types: `Option` collapses to the direct decode (or keep the signature and
  prove `isSome` — implementation's choice; the *semantics* must not have a
  `typeMismatch` branch on decode of elementary types). `loadStorageWordAs`
  (`:2118-2122`) and `coerceStorageWordAs` (`:2124-2138`) lose their decode-failure
  arms for elementary types (aggregate mismatches — an actual `Ty` that has no word
  decode — remain internal errors, they are compiler-invariant violations, not
  environment-reachable states).
- Enum Panic 0x21 must be producible: check `RevertData` has the Panic(0x21) encoding
  (it exists for ABI decode paths — reuse) and route out-of-range **use** of a
  storage-loaded enum through it, matching where solc validates (comparisons,
  conversions, ABI-encode of returns — verified even internal `x == E.B` routes both
  operands through `cleanup_t_enum`).
- **Stage 0 is corpus-observable today, independent of postWorld**: any fixture can
  `sstore` an ill-encoded word via inline assembly and read it back typed. That makes
  it an independently-landable fix with its own Forge-pinned lanes (Stage 0 lanes:
  bool-slot-2 getter returns true; enum-slot-7 getter reverts Panic 0x21; dirty
  address high bits masked; negative intN round-trip; function-type dirty high bytes).

### 2.7 The composition claim

With §§2.1-2.6 landed, our external boundary is shape-identical to Yul's: same shared
`Query`/`Answer` alphabet (already byte-identical via `evm-interaction`), a real
outgoing `OpenWorld` snapshot inside every `Query.external`, wholesale adoption of an
arbitrary `postWorld` on resume satisfying the same round-trip law, and total
evaluation on any adopted state. Therefore the future Solidity→Yul (Sc/Sd) seam can be
stated exactly like the Yul→EVM theorems: `Rel`-style lockstep where both sides expose
the same query and are resumed on the **same unconstrained answer**
(`Interaction.lean:1393-1405`) — reentrancy included, because a reentrant callee is
just one particular environment answer that rewrote our account, and the quantifier
already covers it. No environment well-formedness hypothesis is introduced on our
side, because Yul has none (§1.3), and Stage 0 totality is precisely what makes that
possible.

---

## 3. Responder / fixture format extension

### 3.1 Rows gain an optional postWorld delta

`OracleRow` (`Interpreter.lean:1960-1965`) and the create rows gain an optional `post`
component — deltas, not whole worlds, because **the deltas are model-level: ordinary
slot-keyed writes into the same maps** (orchestrator ruling #1):

```
structure PostDelta where
  selfStorageWrites    : List (Word × Word) := []   -- slot ↦ new word
  selfTransientWrites  : List (Word × Word) := []
  selfBalance?         : Option Word := none        -- absolute, authoritative
  selfNonce?           : Option Word := none
  otherAccounts        : List (Word × OpenAccountDelta) := []  -- balance/code of others
  appendLogs           : List Log.Entry := []       -- callee logs to append
  createdAccounts      : List Word := []
```

Responder semantics: `answerCall?` (`:1979-1998`) — which today wildcards the query's
world — now **takes the sent world** and computes
`postWorld := applyDelta sentWorld row.post`, defaulting (`post` absent) to
`postWorld := sentWorld` — the **echo answer**, exactly `Query.defaultAnswer`'s
convention (`Interaction.lean:709-716`). Same for `answerCreate?` (`:2003-2016`).
Fail-closed rules unchanged: row keying stays (kind, codeAddress, calldata, value,
gas-preference) — the world participates in the *answer*, never in the *match* —
and unmatched requests still error (`:2021-2023`).

Balance interplay with A2's debit (see §4.1): the value-transfer debit currently
applied in `recordExternalInteraction` (balgas `Interpreter.lean:868-899`) is folded
into the responder default: the echo answer's self balance = sent balance − debit
(success-and-kind-dependent, same table as A2). An explicit `selfBalance?` in the row
is authoritative and replaces the debit entirely (no double-count). At Stage 3 the
`recordExternalInteraction` debit is deleted — balance flows only through adoption.

### 3.2 Reentrancy lanes (Forge ground truth)

Method: each lane is a real Forge fixture in `tests/forge-harness/` where the callee
contract actually reenters the caller; the responder row's `post` delta is **derived
from Forge's actual trace** (`forge test -vvvv` storage diffs / final state), and the
Lean side asserts post-call readback. Fixture format per `tests/README.md:39-52`
(rows in manifest `expr` fields; examples at `tests/forge-harness/manifest.json:1550,
1626`).

Pinned lanes:

1. **reentrant-storage-write**: `Victim.pull()` calls `Attacker.notify()`; attacker
   reenters `Victim.setX(42)`. Row: `post.selfStorageWrites := [(slotOfX, 42)]`.
   Assert `x == 42` after the call and the transcript shape.
2. **reentrant-ill-encoded-then-typed-read**: attacker reenters
   `Victim.rawStore(slot, w)` (inline-assembly `sstore`) with `w = 2` into a bool slot
   and `w = 7` into a 3-member enum slot. Post-call: `boolFlag` observably true
   (getter 1); any use of the enum → Panic 0x21. Exercises Stage 0 semantics *through*
   Stage 3 adoption — the marquee lane for the arbitrary-changes model.
3. **balance-changing-callee** (post-A2): callee receives value and sends part back
   (`payable(msg.sender).call{value: …}("")` or `selfdestruct`-funding). Row:
   `post.selfBalance? := traced final balance`. Assert `address(this).balance`
   readback ≠ the naive debit — pins that adoption, not the debit rule, is
   authoritative.
4. **transient-storage-mutation**: victim `tstore(k, 1)`, calls attacker, attacker
   reenters `Victim.bump()` which `tstore(k, tload(k)+1)`; post-call victim
   `tload(k) == 2`. Row: `post.selfTransientWrites := [(k, 2)]`.
5. **create-with-reentry**: `new Child()` whose constructor calls back
   `Victim(msg.sender).setX(7)` before returning. Create row gains the same `post`
   field; assert `x == 7` and the created address. (Expressible today — creation is
   name-encoded initCode, `Interpreter.lean:1838-1848`, but the *response* side is
   ordinary, so the lane works.)

Optional 6th (callee logs): attacker emits an event while reentrant;
`post.appendLogs := [entry]`; assert the canonical log series ordering
(our pre-call event, callee's, our post-call event).

---

## 4. Interaction with the in-flight arcs

### 4.1 A2 balance / A3 gasleft (balgas worktree) — **hard dependency**

Per balgas `docs/DECISIONS.md:1147-1282` and its working tree:

- `State.selfBalance : Word` (balgas `Interpreter.lean:734`) **is the landing spot**
  for `postWorld` self balance (§2.2). Without A2 merged there is nowhere for the
  adopted balance to live — Stage 2+ blocks on A2.
- A2's credit is re-based at each external entry (`evalBodyEntry`, balgas
  `:7623-7629`); adoption happens *within* a frame and simply overwrites
  `selfBalance` mid-body — no interaction with the entry re-basing.
- A2's debit lives in `recordExternalInteraction` (balgas `:868-899`), deliberately
  off the `Stmt.eval` regions. Stage 2 keeps it (echo answers embed the debit, §3.1);
  Stage 3 deletes it in favor of responder-computed postWorld balances. balgas's own
  DECISIONS tail (`:1272-1282`) *names this exact convergence*: "folding `selfBalance`
  into a threaded `OpenWorld` that honours `postWorld`" — this plan is that design.
- A3 (gasleft = `Query.resource .gas`, balgas DECISIONS `:1111-1145`): no semantic
  interaction — resource queries carry no world. One mechanical touch: `runWith`'s
  new `resource` arm (balgas `Interpreter.lean:2105`) sits in the responder region we
  edit; merge mechanics only.

### 4.2 Function-boundary refactor (fnboundary worktree) — **merge mechanics only**

Verified against the fnboundary diff vs base `1a69f5d`:

- Internal calls run **in-monad with no Query emission** (fnboundary
  `Interpreter.lean:7038-7088`, arm comment `:7039-7040`; "transcript invariance",
  fnboundary DECISIONS `:1126-1129`). External-boundary semantics are untouched: no
  hunks at `emitLowLevelCall`/`emitContractCreation`/decoders/`State`/`Context`
  regions (grep of the diff is empty for all those symbols).
- **Zero semantic interaction confirmed.** The reentrancy model is unaffected by
  where internal frames live: a reentrant entry arrives as a fresh *external* entry
  in a separate run (environment's business), not through the internal-call table.
- Merge mechanics: `Stmt.eval` gains a `table` parameter (every caller signature
  changed — ABI.lean, Checked.lean, Interface.lean sites, fnboundary DECISIONS
  `:1103-1115`). Our edits at the emit sites (`:5607-5673, :7122-7208`) and the
  `FunctionDef` entry region will textually collide with both arcs
  (balgas `evalBodyEntry` ~`:7613`; fnboundary `entryInitialFrame?`…`call?`
  ~`:7544-7680`). Plan accordingly: **this work rebases onto the post-merge tree; do
  not start from `1a69f5d`.**

### 4.3 Merge order implication

Either arc may merge first (they were designed disjoint — balgas DECISIONS
`:1185-1193`); this plan needs **both** before Stage 1 lands (Stage 1's snapshot reads
`State.selfBalance`, and starting before fnboundary means rebasing through a
`Stmt.eval` signature change mid-arc). **Stage 0 is the exception**: the per-type read
alignment touches only the decode helpers (`:377-389, :2118-2138, :2373-2399,
:2639-2649`) and expression-level enum validation — disjoint from both arcs' regions —
and may land before, between, or after the merges. Recommended order:
Stage 0 whenever ready → both arcs merge → Stages 1-4.

---

## 5. Staged plan (each stage green: build + `scripts/smoke_replay.sh` per commit; full `FORGE=… scripts/compare_forge_solc_interpreter.sh --jobs 10` at every flip)

**Stage 0 — total, solc-faithful typed reads** (independent; can land now).
Fix the divergences of §2.6: bool total read + nonzero-truthy + encode
canonicalization; enum use-site Panic 0x21 from storage-loaded values; address /
contract / function-type 160-bit masking; intN total signextend; bytesN convention
audit. Land lane+fix together (house style): the Stage 0 assembly-`sstore` lanes
listed in §2.6 pin each divergence against Forge before or with the fix.
Gate: full replay green; new lanes green.

**Stage 1 — real outgoing snapshots** (post-merge; transcript-only).
Implement `snapshotWorld` (§2.1); `emitLowLevelCall`/`emitContractCreation` emit it
instead of `default`. Matchers ignore snapshots (§2.1 corpus-neutrality) — verify by
full replay, not by assumption. Update the checkpoint-1 doc comments (`:1803, 1812,
1899, 1958`). Add one witness pinning a non-default snapshot's self-account contents.
Gate: full replay green with zero fixture edits.

**Stage 2 — adoption wired, echo answers everywhere** (behavior-preserving no-op).
Implement `adoptWorld` (§2.2), `State.selfNonce`, `State.envWorld?` env-read routing
(§2.3), log-prefix mechanism (§2.5). Responders and `contextAnswer` answer
`postWorld := sentWorld` (+ A2-debit fold, §3.1) instead of `default` — the
`defaultAnswer` convention. Since echo-adoption is the identity on every field we
snapshot, behavior is preserved *by the round-trip law*: state and prove
`snapshotWorld context (adoptWorld w context s) = w` and
`adoptWorld (snapshotWorld context s) context s = s` (on carried fields). Audit R1
(events assertions) here.
Gate: both lemmas proved; full replay green with zero fixture edits.

**Stage 3 — the flip: responder deltas + reentrancy lanes.**
`PostDelta` rows (§3.1), `applyDelta`, delete the `recordExternalInteraction` debit
(now subsumed), land the five reentrancy lanes of §3.2 with Forge-traced deltas.
Gate: full `--jobs 10` replay + all new lanes green; A2's balance witnesses updated
to the adoption-authoritative story.

**Stage 4 — register + docs.**
Drop the reentrancy exclusion from the challenge register / gap registry (ROADMAP
rows in the A-series area, `ROADMAP.md:465-473` vicinity); DECISIONS entry recording
the arbitrary-changes decision and superseding `DECISIONS.md:310-319`; ARCHITECTURE
section on the boundary. Gate: docs-only, build green.

---

## 6. Risk register

**R1 — event/witness assertions vs log adoption.** Existing assertions compare
`state.externalInteractions` via `matchesRequest` (kind/target/calldata/value/gas
only, `Call.lean:57-65`) — safe. But assertions on `state.events`
(witness files `SolidCore/Witness/Interface.lean:6897,7023`,
`Checked.lean:13098-14130`; manifest `expr` rows) may assume `events` is cumulative
across calls. §2.5's prefix design can break that under echo answers if `events` is
cleared at adoption. Mitigation: audit all `events`-asserting fixtures at Stage 2;
prefer the split-point variant (keep `events` cumulative, record the adopted prefix
separately) if any fixture depends on cumulativity. Do not edit fixtures to make
Stage 2 pass — Stage 2 must be a true no-op.

**R2 — callee logs and ours.** Yul's answer is unambiguous: the log series is
substate, adopted wholesale (§1.3) — our logs are *not* protected from the
environment. We mirror that (§2.5). The practical containment: fixtures use echo or
append-only deltas, so hostile-rewrite is exercised only by the quantifier in future
theorems, never by lanes. Anyone asserting "our logs survive external calls
unchanged" is asserting a property of the *responder*, not the semantics — document
this in the Stage 4 DECISIONS entry.

**R3 — Context/State split drift.** After Stage 2, `accountBalances`/`accountCodes`/
`accountCodehashes`/`createdInTransactionAccounts` are seeds (§2.3). Risk: a future
env feature reads Context directly and silently ignores adoption. Mitigation: route
all env-fact reads through one accessor that consults `envWorld?` first; doc-comment
the Context fields as seed-only; add a witness where an adopted balance for a third
address differs from the Context seed and the post-call `addr.balance` read sees the
adopted value.

**R4 — responder keying and request fidelity.** `buildCallRequest` (`:1780-1799`)
does not implement delegatecall/staticcall caller/value/permission normalization the
way Yul's `ExternalFrame.callRequest` does (`Interaction.lean:262-306`; staticcall ⇒
`permission := false`, zero apparent value, etc.). Not a postWorld blocker, but the
composition claim (§2.7) eventually needs request-side fidelity too, and fixing it
*changes responder keying* (rows key on the request fields, `:1979-1998`). Keep it
out of this arc; register it as its own follow-on row so it doesn't ride along
silently and break fixtures mid-stage.

**R5 — performance.** `snapshotWorld` materializes the account map per external call;
`WordMap` is an assoc list, and corpus contracts have small storage — O(slots +
accounts) per call is noise at corpus scale (replay gate `--jobs 10` will confirm at
Stage 1). If a pathological fixture appears, snapshot lazily (the snapshot is only
*observed* by responders that use deltas); do not optimize preemptively.

**R6 — "arbitrary changes to OTHER accounts."** Adoption stores them (§2.3) and env
reads honor them; but our other-account model is balance/code-only (no storage). If a
postWorld carries other-account storage we retain it in `envWorld?` (round-trip law)
but nothing reads it — honest, since we never evaluate other contracts' code. No
action; recorded so nobody mistakes retention for interpretation.

**R7 — create response has no `success`.** `decodeCreateResponse` infers failure from
`address == 0` (`:1886-1896`). A failed create's postWorld should conventionally be
the echo world (revert semantics). The responder default does this automatically;
delta rows with `address := 0` plus nonempty deltas are ill-formed — reject in
`applyDelta` (fail-closed responder error, consistent with `:2021-2023` style).

**R8 — shared-package drift.** All boundary types come from `evm-interaction`,
hash-checked against evm-compiler (`scripts/check_shared_interaction_hashes.py`). This
plan adds **no** shared-type changes — everything lands on our side of the seam. If a
future refinement wants delta helpers in the shared package, that is a separate,
coordinated change; do not fork the types.

---

## 7. Dependency summary

| Piece | Depends on A2 (balance) | Depends on fnboundary | Independent |
|---|---|---|---|
| Stage 0 typed reads | — | — | YES (land anytime) |
| Stage 1 snapshot (`selfBalance` field read) | YES | merge mechanics only | — |
| Stage 2 adoption (`selfBalance` landing spot; debit fold) | YES | merge mechanics only | — |
| Stage 3 deltas + lanes (debit deletion; balance lane) | YES | merge mechanics only | — |
| Stage 4 docs/register | — | — | after Stage 3 |

A3 (gasleft): no dependency beyond a textual merge in the responder region.
fnboundary: zero semantic interaction (internal calls emit no queries and touch no
boundary code); cost is purely rebasing through the `Stmt.eval` `table`-parameter
signature change. Start Stages 1+ only from the post-merge tree.
