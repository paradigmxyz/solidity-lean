# Decisions

## 2026-07-07 — perf/storage-map-swap, cause #1: HashMap-backed storage/memory/immutable maps

### Problem
The heaviest storage-read-heavy OZ contracts (openzeppelin-erc20, access-control,
erc1155-pausable-supply, erc721-royalty, erc721-uri-storage) exceeded the 300 s
per-case replay budget (350–700 s single-threaded). Correctness was fine — pure
speed. The dominant driver was O(m·n) storage access:

- `WordMap`/`MemoryMap`/`ImmutableMap` were assoc lists (`List (K × V)`); every
  `lookup?`/`insert` did a linear scan.
- `wordEq lhs rhs := norm lhs == norm rhs` ran **two** bignum `% 2^256` mods per
  comparison, and storage keys are full 256-bit keccak hashes.
- A balance-mapping / EnumerableSet loop doing `m` ops over an `n`-slot store is
  O(m·n) with a bignum constant.

### Change (file:line at commit)
`SolidCore/Solidity/Interpreter.lean`:
- `abbrev StorageMap := Std.HashMap Word Word` (~752) backs `State.storage` /
  `State.transient` (fields ~838–839); `StorageMap.lookup?`/`insertLoop`
  (~754–759) normalize key **and** value at insert and query the HashMap in O(1)
  expected. `State.loadSlot`/`storeSlot`/`loadTransientSlot`/`storeTransientSlot`
  and `State.empty`/`clearTransient` updated to the new type.
- `abbrev MemoryMap := Std.HashMap Nat Value` (~797) backs `Runtime.memory`.
- `abbrev ImmutableMap := Std.HashMap String Value` (~808) backs
  `State.immutables`.
- `Repr` instances for the three (render via `toList`) since `State`/`Runtime`
  derive `Repr`.
- `WordMap` (assoc list) **kept** — it now backs only the small, cold `Context`
  seed maps (`accountBalances`/`accountCodehashes`), which are iterated by key at
  snapshot boundaries and read via `Account.lookupWord?`.
- Bridges `wordMapToStorage`/`storageToWordMap` (~1961) rewritten for the HashMap
  (fold / `toList.foldl`).

`SolidCore/Solidity/AdoptionLaws.lean`: the adoption round-trip meta-theorems
(`lookup?_roundtrip`, `find?_wordMapToStorage`, `lookup?_storageToWordMap`, and
`adoptWorld_echo_noop`) reproved for the HashMap representation. They gained a
`StorageMap.WF` (canonical-keys/values) hypothesis — required because the new
`StorageMap.lookup?` matches keys by exact `norm`-query equality, so the law is
false for a hand-built HashMap with a non-canonical physical key; **every**
interpreter-built `StorageMap` is WF (keys/values normalized at every insert;
`{}` trivially). No `sorry`/axioms.

Lean witness expressions adapted to the new types (not the frozen `.sol` corpus
or Forge tests): `State` literals in `Witness/InterpreterExamples.lean`,
`.transient.isEmpty` in `Witness/Interface.lean` and `Witness/Checked.lean`, and
`state.storage.toList` one-entry matches in `tests/forge-harness/manifest.json`
(a one-entry HashMap's `toList` is `[(k, v)]`, so the exactness check is
preserved).

### Correctness / order audit (the #1 risk of this change)
Keys and values are normalized (`% 2^256`) at **insert** time, so two Nats equal
mod 2^256 collide as one key — exactly what `wordEq`-on-compare guaranteed — and
reads never re-`norm`. HashMap iteration order is nondeterministic, so I audited
every consumer of the three maps for order dependence:

- **storage / transient**: the only iterations are `wordMapToStorage` (folds into
  the key-addressed `EvmYul.Storage`; keys are unique after dedup, so fold order
  is irrelevant) and `storageToWordMap` (rebuilds from the key-addressed store).
  No `.toList`/fold of these maps feeds observable output directly. ✅
- **memory**: keyed by monotonic allocation id; only ever read/written by id
  (`Runtime.loadMemory?`/`allocMemory`/`storeMemory?`), never iterated. ✅
- **immutables**: read by name only (`State.immutable?`), never iterated. ✅
- **Context.accountBalances/accountCodehashes**: iterated by key in
  `snapshotOtherAccounts` — left as assoc lists (`WordMap`), so their order
  behavior is untouched. ✅

Conclusion: no observable result changes.

### Gates
- `lake build SolidCore` — green (1097 jobs), `AdoptionLaws` fully proven, no
  `sorry`/axioms.
- `scripts/smoke_replay.sh` (SOLC pinned to 0.8.35) — 28/28 `lean=ok`,
  `forge_interpreter_compare=pass`.
- Heavy case `openzeppelin-erc20` (`--jobs 1 --skip-forge --timeout 1800`):
  `lean=ok`, `forge_interpreter_compare=pass`.
  - **Before**: ~695 s wall / 437 s user.
  - **After**: 391 s wall / 383 s user.
  - The residual is dominated by fixed Lean elaboration/`#eval` compilation of the
    generated contract, not storage access.

### Follow-ups (not done — deliberately out of scope for this commit)
- **Cause #2**: `FunctionTable.lookup?`/`lookupById?` are O(F) `List.find?` scans
  (string compare / bignum `wordEq`) per internal call. Build name→fn and id→fn
  indexes once at construction. (Prototyped and green in a scratch pass:
  `FunctionTable` becomes a struct `{ entries, byName, byId }` built via a
  first-match `insertIfNew` fold; needs a `Coe (List InternalFunction)
  FunctionTable` for the hand-built witness tables and `[]`→`{}` at empty-table
  call sites in the witness files.)
- **Cause #3**: `Ty.storageValueFromWord?` re-`norm`s an already-canonical loaded
  word and recomputes `2^(8n)` per `fixedBytes` read. Since post-cause-#1 stored
  words are canonical, the redundant second `norm` can be dropped (masking
  semantics unchanged). Lower priority.
