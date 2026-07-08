# Implementation-level solc-vs-Solidus divergence review (round 7 — runtime behavior)

**Seventh implementation-level pass.** Rounds 1–6 covered arithmetic / cleanup /
conversion helpers, the ABI encode+decode codec, the analysis-pass ACCEPTANCE
rules, and value-producing codegen (selectors / slices / builtins — round 6
surfaced V1 calldata-slice-OOB and A1 abstract-`interfaceId`, both now in-flight).
This round traces the **runtime SEMANTICS** those rounds did not: inheritance /
C3 linearization / override dispatch / `super` chain, base-constructor &
state-variable **initialization order**, modifier substitution/chaining,
fallback/receive dispatch, storage-slot computation, `delete` of complex storage,
and `abi.encodeCall` / precompile framing.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit
`47b9dedd`, READ-ONLY — the exact source of this project's pinned binary).
Solidus at `codex/solidity-semantics-only` HEAD `c2009b8`. Canonical semantics
files are `SolidCore/Solidity/*.lean` (+ importer
`scripts/solc_ast_to_lean_source.py`). Nothing was built or run for Solidus;
tiny probes used the pinned `solc 0.8.35`
(`/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35`) — in particular a
`--combined-json storage-layout` probe to nail the headline finding. Findings are
**CONFIRMED** (both sides read to the rule, + probe / executable simulation) or
**INFERRED** (deduced from a code trace).

---

## Executive summary

**Surfaces read this round (code, not tests), both sides:**

- **C3 linearization / override dispatch / `super`** — Solidus
  `dispatchOrderWithFuel?` + `mergeLinearizationsWithFuel?` + `findMergeCandidate?`
  (`Interface.lean:18332-18365`), override winner via first-match over
  derived-first `functions` (`findFunctionBySelector?`/`findFunctionByName?`
  `Interpreter.lean:8913-8927`; `dedupInternalByName` `Interface.lean:19000-19010`),
  `super` helpers over the whole-contract dispatch order
  (`contextualSuperHelpersFor?` `Interface.lean:17997-18003`) ↔ solc
  `cThreeMerge`/`linearizeBaseContracts` (`NameAndTypeResolver.cpp:422-497`).
- **Constructor & state-var init order** — per-contract `initStmts ++ [bodyCore]`
  (`Interface.lean:19116-19203`) composed over `storageOrder`
  (`Interface.lean:19902-19926`) ↔ solc most-base-first ctor order + inline
  initializers.
- **Storage layout order** — `storageOrderWithFuel?` (`Interface.lean:18267-18282`)
  drives slot assignment (`stateVars := concatMapList directStateVars storageOrder`
  `:19314`) ↔ solc `ContractType::stateVariables()` iterating
  `linearizedBaseContracts | reverse` (`Types.cpp:2168-2172`).
- **Modifier semantics** — `functionExpandModifiersToCoreWithInternalCallsFull?`
  (`Interface.lean:15840-15872`), `modifierApplyToCoreWithInternalCalls?`
  (`:15812-15838`), `_`→continuation with `captureReturn`
  (`Stmt.toCoreReplacingModifierPlaceholder?` `:7068-7073`).
- **Fallback / receive dispatch** — `callCalldataAtFromWithContext?` +
  `callReceiveOrFallbackAtFromWithContext?` (`ABI.lean:633-707`).
- **Storage-slot math + `delete`** — mapping/array slot keccak
  (`Interpreter.lean:1727-1752`), `clearStorageLayoutAt` (`:3509-3534`).

**Headline: this round found a second wrong-VALUE divergence — DL1 — a wrong
storage-slot layout (and wrong constructor/init order) for a non-trivial diamond,
caused by Solidus computing the storage/constructor order with a naive DFS instead
of the reverse C3 linearization.**

- **DL1 (NEW, SOUNDNESS wrong-value + wrong-order, DIFFERENTIALLY-LIVE,
  CONFIRMED)** — Solidus's `storageOrder` (`storageOrderWithFuel?`) is a
  left-to-right **DFS post-order keep-first dedup**, but solc lays out storage (and
  runs constructors / inline initializers) in **`reverse(linearizedBaseContracts)`**
  = reverse C3. These coincide for simple diamonds but **diverge** whenever a
  contract lists a direct base that is also an indirect base positioned so DFS
  pulls a shared base to a different rank than C3. Minimal repro (solc-probe
  CONFIRMED): `contract X{uint x;} contract Y{uint y;} contract M is X,Y{uint m;}
  contract Z is Y,M{uint z;}` — solc lays out `x@0, y@1, m@2, z@3`; Solidus
  assigns `y@0, x@1, m@2, z@3` (**x and y swapped**). Consequences: **wrong storage
  slot for every affected variable → wrong VALUES on read/write and a wrong
  external storage-layout**, plus **wrong constructor / inline-initializer
  execution order** (observable when an initializer has a side effect or reads
  another base's value).

Everything else read this round is **faithful**: the C3 *dispatch* order (used for
override/`super` resolution) matches solc **exactly** (verified by executable
simulation across the classic C3 stress hierarchies + the diamond), the override
winner is always the most-derived (first-match over derived-first tables), the
`super` chain follows the most-derived MRO (all `__super_X_f` helpers computed
against the single whole-contract dispatch order), modifier substitution /
chaining / arg-timing / `captureReturn` are correct, fallback/receive precedence
is correct (receive only on empty calldata; 1–3 bytes and no-match → fallback),
and mapping/array slot math + `delete` (mapping-in-struct skipped, arrays/bytes
cleared) are correct.

| # | Target | Verdict | Severity | Reachability |
|---|--------|---------|----------|--------------|
| **DL1** | storage-slot layout + ctor/init order for non-trivial diamond | **DFS order ≠ reverse-C3 → wrong slots + wrong init order** | **SOUNDNESS (wrong value + wrong order)** | **DIFFERENTIALLY-LIVE** (untested in corpus) |
| F1 | C3 *dispatch* order (override/`super` MRO) | faithful (matches `cThreeMerge`, sim-verified) | — | n/a |
| F2 | override winner (external/internal/name) | faithful (first-match, derived-first) | — | n/a |
| F3 | `super.f()` diamond chain | faithful (whole-contract MRO) | — | n/a |
| F4 | modifier `_`/chaining/arg-timing/return | faithful | — | n/a |
| F5 | fallback / receive dispatch precedence | faithful | — | n/a |
| F6 | mapping/array slot math + `delete` complex storage | faithful | — | n/a |

**NEW findings this round: 1 differentially-live (SOUNDNESS wrong-value +
wrong-order), 0 importer-masked.** Combined with round 6's V1, this is the second
wrong-VALUE divergence of the campaign — and it strikes the richest unexplored
runtime surface exactly where the coordinator predicted (inheritance ordering).

---

## DL1 — storage-slot layout & constructor/init order diverge for a non-trivial diamond (DFS order ≠ reverse-C3) — SOUNDNESS (wrong value + wrong order)

### The two algorithms

**solc.** State variables are laid out (and constructors + inline initializers
run) most-base-first, in **`reverse(linearizedBaseContracts)`** where
`linearizedBaseContracts` is the C3 linearization (derived-first,
`NameAndTypeResolver.cpp:422-497`). Layout iteration:
`Types.cpp:2168-2172`:

```cpp
for (ContractDefinition const* contract:
        m_contract.annotation().linearizedBaseContracts | ranges::views::reverse)
    for (VariableDeclaration const* variable: contract->stateVariables())
        ... variables.push_back(variable);
```

Constructor / initializer order is the same reverse-C3 (most base first).

**Solidus.** `storageOrder` is computed **independently** of the C3 dispatch order,
by a left-to-right DFS post-order with keep-first dedup
(`ContractDecl.storageOrderWithFuel?`, `Interface.lean:18267-18282`):

```
bases ← ContractDecl.baseDecls? contracts decl          -- direct bases in SOURCE order
baseOrders ← map (storageOrderWithFuel? …) bases
some (appendUniqueContracts [] (concatLists baseOrders ++ [decl]))   -- DFS + dedup keep-first
```

This `storageOrder` then drives **slot assignment**
(`stateVars := concatMapList ContractDecl.directStateVars storageOrder`,
`Interface.lean:19314`; packed via `storageFieldAndNext`) **and constructor
composition** (`pieces ← mapOption (constructorBodyForDeployment? …) storageOrder`,
`Interface.lean:19902-19926`, with each contract contributing
`initStmts ++ [bodyCore]`).

The importer **drops** solc's `linearizedBaseContracts` (it is in
`METADATA_SCALAR_FIELD_SUFFIXES`, `solc_ast_to_lean_source.py:42`), so Solidus
recomputes both orders from `decl.bases` — the DFS storage order is genuinely
Solidus's own, not solc's.

Note Solidus's **dispatch** order *is* correct C3 — `dispatchOrderWithFuel?`
(`Interface.lean:18346-18365`) reverses the direct bases and merges via
`mergeLinearizationsWithFuel?`/`findMergeCandidate?` (`:18301-18344`), whose
candidate rule ("first head that appears in no list's tail") is **identical** to
solc's `cThreeMerge` `appearsOnlyAtHead`/`nextCandidate`
(`NameAndTypeResolver.cpp:452-472`). The bug is specifically that `storageOrder`
uses a *different, non-C3* traversal instead of `reverse(dispatchOrder)`.

### Divergence (executable simulation + solc probe)

A faithful re-implementation of all three algorithms (solc C3, Solidus dispatch,
Solidus storage) agrees on the *dispatch* order for every hierarchy tried but
diverges on *storage* order for non-trivial diamonds. Classic C3-stress
hierarchy `O; A,B,C,D,E is O; K1 is A,B,C; K2 is D,B,E; K3 is D,A; Z is K1,K2,K3`:

- Solidus **dispatch** = solc linearization = `Z,K3,K2,E,K1,C,B,A,D,O` (MATCH).
- solc **storage** (reverse-C3) = `O, D, A, B, C, K1, E, K2, K3, Z`.
- Solidus **storage** (DFS) = `O, A, B, C, K1, D, E, K2, K3, Z` — **`D` is misranked**.

**Minimal repro (solc-probe CONFIRMED):**

```solidity
contract X { uint256 x; }
contract Y { uint256 y; }
contract M is X, Y { uint256 m; }
contract Z is Y, M { uint256 z; }
```

`solc --combined-json storage-layout` for `Z`:
`x@slot0, y@slot1, m@slot2, z@slot3`.

Solidus `storageOrder(Z)`: bases `[Y, M]` (source order) →
`storageOrder(Y)=[Y]`, `storageOrder(M)=[X,Y,M]` → `[Y]++[X,Y,M]++[Z]` dedup
keep-first = `[Y, X, M, Z]` → **`y@slot0, x@slot1, m@slot2, z@slot3`**.

So `x` and `y` land on **swapped slots**. The trigger is common: a contract
(`Z`) lists a direct base (`Y`) that is *also* an indirect base (via `M is X, Y`),
with the shared base positioned so DFS keep-first ranks it before C3 does.

### Consequences (why it is a wrong VALUE, not just cosmetic)

1. **Wrong storage slots.** Any read/write of an affected state variable hits the
   wrong slot. In the minimal repro, writing `x` in Solidus writes solc's `y`
   slot. Observable at the external boundary (a getter returning `x`, or a raw
   `sload` view of the layout) and across `delegatecall`/upgrade layout matching.
2. **Wrong constructor / inline-initializer order.** `pieces` is mapped over
   `storageOrder`, so base constructors and inline `uint256 x = f();` initializers
   run in DFS order, not reverse-C3. When an initializer has a side effect (event,
   storage write) or reads another base's already-initialized value, the observable
   result differs.

### Reachability & classification

**DIFFERENTIALLY-LIVE.** solc compiles the repro (probe: no errors, storage
layout emitted); Solidus accepts it (dispatch C3 succeeds) and mis-lays-out /
mis-orders. Not importer-masked — the importer produces the AST and Solidus's own
Lean recomputation is wrong. **Untested in the corpus** (no such diamond present),
so currently unflagged by the differential harness. **Severity: SOUNDNESS
(wrong value + wrong order).** **Confidence: CONFIRMED** (solc probe + Solidus
code trace + executable simulation of all three orderings).

### Suggested fix (for the sibling fix-agent — not applied here)

Define the storage/constructor order as **`reverse(dispatchOrder)`** (reverse of
the already-correct C3 linearization) rather than the independent DFS
`storageOrderWithFuel?`. Concretely, replace `ContractDecl.storageOrder?` with
`(ContractDecl.dispatchOrder? contracts decl).map List.reverse`, and audit the two
call sites (slot assignment `:19314`, constructor composition `:19902-19926`) to
consume the reversed C3 order. This makes storage layout and init order agree with
solc while leaving the (already-faithful) dispatch order untouched.

---

## Faithful surfaces (earned negatives this round)

- **F1 — C3 dispatch order.** `mergeLinearizationsWithFuel?` +
  `findMergeCandidate?`/`findMergeCandidateLoop?` (`Interface.lean:18301-18344`)
  implement exactly solc's `cThreeMerge` (`NameAndTypeResolver.cpp:449-497`): the
  candidate is the first list-head that appears in no list's tail, lists scanned in
  the same order (`baseOrders ++ [reverse bases]`); `decl` prepended matches solc
  putting the contract at the head of its direct-bases list. Executable simulation
  confirms Solidus dispatch order == solc linearization on the diamond and the
  full C3-stress hierarchy.
- **F2 — override winner.** External dispatch `findFunctionBySelector?` and
  name/internal dispatch `findFunctionByName?` are `List.find?` (first match) over
  `contract.functions`, which is built derived-first (`functionGroups` mapped over
  `dispatchOrder`, `Interface.lean:19492-19498`, `19554-19567`); the internal
  table dedups keep-first (`dedupInternalByName`, `:19000-19010`). The most-derived
  override always wins — matching solc.
- **F3 — `super` diamond chain.** `super.f()` in `C` rewrites to `__super_C_f`
  (`Interface.lean:325-354`); every `__super_X_f` helper is built from
  `afterName? dispatchOrder X.name` over the **single whole-contract**
  `dispatchOrder` (`contextualSuperHelpersFor?` `:17997-18003`,
  `contextualSuperHelpers?` mapped over all of `dispatchOrder`). So a base reached
  via `super` continues along the *most-derived* contract's MRO, not its own —
  the correct C3 `super` semantics.
- **F4 — modifiers.** Chaining folds right (first-listed = outermost:
  `functionExpandModifiers…Full?` recurses on `rest` then wraps with the current
  invocation, `:15862-15871`). `_` is replaced by the continuation wrapped in
  `captureReturn` (`:7071-7073`) so a `return` in the body sets return vars and
  resumes the modifier after `_`; multiple `_` each expand; a `_` inside an `if`
  conditionally skips the body. Modifier arguments are bound as a `prefix` before
  the body (`modifierParamBindingsWithArgs?`, `:15823`), i.e. evaluated when the
  modifier is entered — matching solc.
- **F5 — fallback / receive dispatch.** `callCalldataAtFromWithContext?`
  (`ABI.lean:676-707`): `readSelector?` needs ≥4 bytes → selector match →
  function, else fallback; <4 bytes → `callReceiveOrFallback?`, which routes to
  **receive only when `calldata.isEmpty`** (else fallback), with the payable/value
  gate via `acceptsValue`/`rejectedValueCall?`. Matches solc's precedence (receive
  ⇔ empty calldata; 1–3 bytes and no-match ⇒ fallback).
- **F6 — slot math + `delete`.** Mapping slot `keccak(h(k)‖slot)` for value keys
  and `keccak(keyBytes‖slot)` for `bytes`/`string` keys (`Interpreter.lean:1727,
  1745`); dynamic-array data base `keccak(slot)` (`:1752`). `delete` clears
  scalars/packed/struct-fields/fixed+dynamic arrays/bytes/string and **skips
  mappings** (`clearStorageLayoutAt`, `:3509-3534`: `mapping _ _ => Except.ok
  state`), so `delete structWithMapping` leaves the mapping intact — matching solc.

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] C3 linearization / override dispatch / `super` chain — **dispatch FAITHFUL**
  (F1/F2/F3, sim-verified)
- [x] Storage-slot layout order — **WRONG (DFS ≠ reverse-C3)** (DL1, NEW)
- [x] Base-constructor & state-var init order — **WRONG order (same root cause as
  DL1)**
- [x] Modifier `_`/chaining/arg-timing/conditional-skip/return — **FAITHFUL** (F4)
- [x] Fallback / receive dispatch precedence — **FAITHFUL** (F5)
- [x] Mapping/array/bytes storage-slot math — **FAITHFUL** (F6)
- [x] `delete` of complex storage (struct-with-mapping, dyn/fixed arrays) —
  **FAITHFUL** (F6)

**Still NOT reached (worklist for a future pass):**

- `abi.encodeCall` full argument-tuple **type-match** acceptance (the selector +
  arg-encoding path is faithful; the arity/implicit-conversion acceptance rule
  against the function-pointer's declared params was not exhaustively traced).
- Precompile **input framing** beyond ecrecover/sha256/ripemd160 spot-checks
  (modexp 0x05 length-prefix layout, ecadd/ecmul/pairing point encodings,
  blake2f, point-eval) — these are responder-answered; only Solidus's own
  calldata framing would be the divergence surface.
- Storage **packing across the inheritance boundary** in the presence of DL1 — the
  packing cursor itself was read (`storageFieldAndNext`, `:18401`) and is faithful
  per-order, but its interaction with a *corrected* order should be re-audited when
  DL1 is fixed.
- Transient storage (`tstore`/`tload`) slot allocation order (uses the same
  `storageOrder`/transient cursor; would inherit DL1's mis-order for transient
  vars across a diamond) — not separately probed.

---

## Bottom line

The seventh pass targeted runtime behavior — the richest unexplored surface — and
found **DL1**, the campaign's second wrong-VALUE divergence: Solidus assigns
storage slots (and sequences base constructors + inline initializers) in a naive
left-to-right **DFS order** rather than solc's **reverse C3 linearization**. The
two agree for simple diamonds but diverge for a common pattern — a contract that
lists a direct base which is also an indirect base — producing **swapped storage
slots** (wrong values on read/write and a wrong external layout) and a **wrong
constructor/initializer order**. Minimal repro `Z is Y, M / M is X, Y` is
solc-probe confirmed (`x@0,y@1` in solc vs `y@0,x@1` in Solidus). The fix is to
derive the storage/constructor order as `reverse(dispatchOrder)` — the C3 order
Solidus *already* computes correctly for dispatch. Every other runtime surface
read — C3 dispatch order, override winner, the diamond `super` chain, modifier
substitution/chaining/return, fallback/receive precedence, and slot-math/`delete`
of complex storage — is **faithful**.

**NEW divergences this round: 1 differentially-live (SOUNDNESS wrong-value +
wrong-order), 0 importer-masked.**
