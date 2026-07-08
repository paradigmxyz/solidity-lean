# Implementation-level solc-vs-Solidus divergence review (round 11 — create / create2 / selfdestruct observables + precompile input framing)

**Round 11 of the campaign** (the ninth `divergences-*` doc). Round-10
(transient-storage slot ORDER + storage-packing re-audit) is **deferred**: it
rides the DL1 fix (reverse-C3 storage order), which is still open on `main` per the
git log — reviewing transient order now would only re-derive DL1's already-reported
DFS-vs-reverse-C3 bug for transient vars. This round instead executes the plan's
Round-11: the execution **observables** of `new C{value,salt}(args)`,
`selfdestruct(a)`, and the calldata **framing** Solidus emits for precompile
staticcalls (0x01–0x0a) — the open-world/postWorld model re-derives create/destroy
balance-and-address observables (the V1 class), and a mis-framed precompile input
is a value re-derivation.

solc source read (v0.8.35, `/Users/dan/Projects/solidity-src`, commit `47b9dedd`,
READ-ONLY — the exact source of the pinned binary). Solidus at branch
`codex/solidity-semantics-only` HEAD. Canonical semantics are
`SolidCore/Solidity/*.lean` + `SolidCore/Solidity/Shared/*.lean`. Nothing was
built/run for Solidus. Findings are **CONFIRMED** (both sides read to the rule +
EVM/solc ground truth) or **INFERRED** (code trace).

---

## Executive summary

**Surfaces read this round (code, both sides):**

- **`new C(...)` create observables** — `emitContractCreation` →
  `decodeCreateResponse` (`Interpreter.lean:2382-2408`), success `= address != 0`;
  plain-create failure bubble `RevertData.fromRawBytes result.output`
  (`:6459`, `:6477`); try-create success/address bind (`:8439-8447`) ↔ solc
  `FunctionType::Kind::Creation` (`IRGeneratorForStatements.cpp:1581-1649`):
  `create`/`create2` + `if iszero(address) { forwardingRevert() }`.
- **Create value transfer** — responder debit `debitWorldSelf` fed by
  `ExternalInteraction.selfBalanceDebit` (`= result.value` on a successful create,
  `Interpreter.lean:1046-1047`, applied in `answerCreate?` `:2661-2677`), new-account
  credit via the answered `postWorld` ↔ EVM create value move.
- **`selfdestruct(a)`** — `Stmt.selfdestruct` → `State.recordSelfdestruct`
  (`Interpreter.lean:8519-8532`, `940-951`) + `selfdestructRecord`
  (`Shared/Account.lean:71-79`) with EIP-6780 `deletesAccount` ↔ EVM `SELFDESTRUCT`.
- **Precompile input framing** — `ecrecoverInput`, `modexpInput`
  (`Shared/Precompile.lean:89-105`); the live builtin staticcalls (ecrecover/
  sha256/ripemd160, `emitPrecompileWord` `Interpreter.lean:2313-2319`) ↔ EIP layouts.

**Headline: one modeling gap found — CS1 — `selfdestruct` does not move balance.**
`recordSelfdestruct` records the `(from, recipient)` pair and the EIP-6780
`deletesAccount` flag, but it does **not** zero the self balance nor credit the
recipient. The EIP-6780 delete/no-delete decision and the selfdestruct-set are
faithful; only the balance transfer (which the EVM performs unconditionally,
delete or not) is unmodeled.

- **CS1 (NEW, SOUNDNESS-conditional / COMPLETENESS, reachability UNTESTED,
  CONFIRMED-by-trace)** — see below. Unlike `call`/`create` value transfer (which
  is modeled through the responder's `debitWorldSelf` + answered `postWorld`),
  `selfdestruct` emits no query, so no balance flows on either side: self keeps its
  pre-destruct balance and the recipient is uncredited. Live only if the
  differential harness compares post-selfdestruct account balances (the witness
  suite currently asserts only the record fields + a storage slot).

Everything else read is **faithful**: the deployed-contract address and success
flag are responder-answered with solc's exact `iszero(address)` success rule;
plain-`new` constructor-revert bubbles the raw returndata byte-for-byte like
`forwardingRevert` (empty→empty); try-`new` binds the address / runs the catch
clause on failure; create **value transfer** debits self and credits the new
account through the responder; the **EIP-6780** selfdestruct delete flag matches
(`!cancunOrLater || createdThisTx`); and precompile **input framing** is either
correct (`ecrecoverInput` = digest‖v‖r‖s for 0x01; `modexpInput` = the EIP-198
length-prefixed layout) or **not a live re-derivation surface** at all — 0x05–0x0a
have no Solidus builtin, so their calldata is constructed by the Solidity source
and merely passed through to the responder.

| # | Target | Verdict | Severity | Reachability |
|---|--------|---------|----------|--------------|
| **CS1** | `selfdestruct` balance transfer (self→recipient) | **not modeled (self not zeroed, recipient not credited)** | **SOUNDNESS-cond. / COMPLETENESS** | **UNTESTED** (live iff post-destruct balances compared) |
| F1 | `new` deployed address + success (`iszero`) | faithful (responder-answered, exact rule) | — | n/a |
| F2 | plain-`new` constructor-revert bubble | faithful (raw forward, empty→empty) | — | n/a |
| F3 | try-`new` success/address bind + catch | faithful | — | n/a |
| F4 | create value transfer (debit self / credit new) | faithful (responder debit + postWorld) | — | n/a |
| F5 | `selfdestruct` EIP-6780 delete flag | faithful (`!cancun ∨ createdThisTx`) + set | — | n/a |
| F6 | precompile input framing (0x01 ecrecover, 0x05 modexp) | faithful; 0x05–0x0a not live (source-framed) | — | n/a |
| F7 | create2 deployed address prediction | OOS by decision (G22; name-encoded initCode) | — | OOS |

**NEW findings this round: 1 (SOUNDNESS-conditional / COMPLETENESS,
reachability-UNTESTED, CONFIRMED-by-trace), 0 wrong-value differentially-live.**

---

## CS1 — `selfdestruct` does not transfer the self balance to the recipient

### solc / EVM

`SELFDESTRUCT(recipient)` transfers the **entire** balance of the executing
account to `recipient` **unconditionally** — before and after EIP-6780. Post-Cancun
EIP-6780 only changes whether the *account* is deleted (deleted iff created in the
same transaction); the balance is still sent (so a non-created-this-tx contract
keeps code but ends with balance 0, and `recipient.balance` grows by the old self
balance). solc lowers `selfdestruct(a)` directly to the `selfdestruct(a)` opcode
(`IRGeneratorForStatements.cpp` builtin), so the EVM performs the transfer.

### Solidus

`Stmt.selfdestruct` (`Interpreter.lean:8519-8532`) evaluates the recipient and
returns `Result.selfdestructed` after `State.recordSelfdestruct`
(`Interpreter.lean:940-951`):

```lean
def State.recordSelfdestruct (state) (evmVersion) (createdAccounts) (self recipient) :=
  let record := selfdestructRecord evmVersion createdAccounts self recipient
  { state with
    selfdestructs := state.selfdestructs ++ [(record.fromAddress, record.recipient)]
    selfdestructEffects := state.selfdestructEffects ++ [record]
    worldMutatedSinceAdoption := true }
```

`selfdestructRecord` (`Shared/Account.lean:71-79`) computes only
`{fromAddress, recipient, deletesAccount}` — no amount. **Nothing zeroes
`State.selfBalance`, and nothing credits the recipient account.** The snapshot
projection carries `State.selfBalance` verbatim (`DECISIONS.md` 2085-2086,
`snapshotSelfAccount`) and overlays only the selfdestruct *set*, live self account,
and logs (`snapshotWorld` `Interpreter.lean:2108-2128`) — the self balance in the
outgoing world is the pre-destruct value, and the recipient (an other-account read
from the seed maps / adopted world) is never incremented.

Contrast the **value-carrying `call`/`create`** path, which *is* modeled: the
responder's `answerCall?`/`answerCreate?` apply `debitWorldSelf` using
`ExternalInteraction.selfBalanceDebit` (`= result.value`, `Interpreter.lean:1037-1047`,
`2624-2640`, `2661-2677`) and the new account is credited by the answered
`postWorld`. `selfdestruct` has no analogous debit/credit because it emits no query
(no `Query.external`), so the balance move is simply absent.

### Reachability & classification

**UNTESTED.** The selfdestruct witnesses
(`Witness/Interface.lean:6371-6433`, `Witness/Checked.lean:7950-7978`) assert only
the record fields (`from`, `recipient`, `deletesAccount`) and a storage slot — no
post-destruct balance is compared, so no current witness would catch this. It
becomes **SOUNDNESS-live** iff the differential harness observes the self
account's balance after a top-level selfdestruct (EVM: 0 or account-gone; Solidus:
unchanged) or the recipient's balance (EVM: credited; Solidus: unchanged). It is a
genuine EVM observable, so it is not OOS the way access-sets/refund are (those are
explicitly declared gaps in `DECISIONS.md` 2091-2093; the selfdestruct balance move
is not). **Severity: SOUNDNESS-conditional** (wrong balance if observed), else
COMPLETENESS. **Confidence: CONFIRMED-by-trace** — `recordSelfdestruct` provably
does not touch balances, and the balance transfer is EVM spec.

### Suggested fix (for a fix-agent — not applied here)

On `Stmt.selfdestruct`, before halting: read `self`'s balance `b`, set
`State.selfBalance := 0`, and credit `recipient` by `b` in the world (the same
`debitWorldSelf`-style overlay used for value transfer, but a *credit* to the
recipient and a *zero* of self). Under EIP-6780 the account-deletion flag already
computed by `selfdestructRecord` stays as-is; only the balance move is added.
Guard the self==recipient degenerate case (net zero).

---

## Faithful surfaces (earned negatives this round)

- **F1 — `new` address + success rule.** `decodeCreateResponse`
  (`Interpreter.lean:2382-2392`) sets `success := address != 0` and carries the
  responder's `address`/`returnData`; solc's non-try create ends with
  `if iszero(<address>) { forwardingRevert() }` (`IRGeneratorForStatements.cpp:1621`)
  and try-create with `let success := iszero(iszero(<address>))` (`:1619`). Same
  success rule; the address is EVM/responder ground truth on both sides.
- **F2 — plain-`new` constructor-revert bubble.** On failure Solidus throws
  `RevertData.fromRawBytes result.output` (`:6459`, `:6477`); `fromRawBytes`
  (`:305-309`) → `empty` iff output empty else `raw output`. solc's
  `forwardingRevert` (`YulUtilFunctions.cpp:4147-4172`) forwards the raw returndata
  verbatim (empty→`revert(0,0)`). Byte-for-byte identical bubble of the
  constructor's `Error`/`Panic`/custom/empty revert.
- **F3 — try-`new`.** `Stmt.tryContractCreate` (`Interpreter.lean:8439-8473`):
  on success binds the address to the (optional) returns var and runs `successBody`;
  on failure routes the raw output through `TryCatchClause.findMatch?` then bubbles
  `fromRawBytes` if unmatched — the same dispatch as `tryExternalCall` (see round 9;
  the CB1 Error-clause gate applies here too, noted for the fix-agent).
- **F4 — create value transfer.** `selfBalanceDebit` returns `result.value` on a
  successful create (`:1046-1047`); `answerCreate?` folds it into the echoed world
  via `debitWorldSelf` (`:2661-2669`), and the new account's balance arrives in the
  answered `postWorld`. So `new C{value:v}()` debits the creator by `v` and credits
  the deployee — the create balance move IS modeled (unlike selfdestruct).
- **F5 — EIP-6780 selfdestruct delete flag + set.** `selfdestructDeletesAccount`
  (`Shared/Account.lean:66-69`) = `!evmVersion.cancunOrLater || createdThisTx`,
  matching EIP-6780; witnesses confirm Cancun-no-delete, pre-Cancun-delete, and
  Cancun-created-this-tx-delete (`Witness/Interface.lean:6384-6433`). The
  selfdestruct SET is projected into substate `selfDestructSet`
  (`snapshotWorld` `:2118-2121`), matching EVM substate.
- **F6 — precompile input framing.** `ecrecoverInput` (0x01) =
  `digest‖v‖r‖s` and `modexpInput` (0x05) = `len(base)‖len(exp)‖len(mod)‖
  base‖exp‖mod` (`Shared/Precompile.lean:89-105`) are the exact EIP layouts. Per
  the 2026-07-06 precompile-alignment decision (`Shared/Precompile.lean:81-87`),
  precompiles are ordinary external calls answered by the responder; only
  ecrecover/sha256/ripemd160 have live builtins (`emitPrecompileWord`
  `:2313-2319`, framing the ecrecover input). **0x05–0x0a have no Solidus builtin**
  — their calldata is built by the Solidity source (`abi.encodePacked`, etc.) and
  passed through a raw `staticcall`, so there is **no Solidus-side framing
  re-derivation to diverge** (the plan's suspected surface resolves to N/A);
  `modexpInput` is a correct-but-witness-only helper.
- **F7 — create2 address prediction.** OOS by decision (G22): identity is the
  name-encoded `creationInitCode` (`Interpreter.lean:2342-2344`), not compiled
  bytecode, so the CREATE2 `keccak(0xff‖deployer‖salt‖keccak(initcode))` address is
  responder-answered rather than re-derived — a declared limitation, not a bug.

---

## Surfaces reviewed vs still-not-reached

**Reviewed this round (both sides; verdict noted):**

- [x] `new` deployed address + `iszero(address)` success rule — **FAITHFUL** (F1)
- [x] plain-`new` constructor-revert bubbling — **FAITHFUL** (F2)
- [x] try-`new` success/address bind + catch dispatch — **FAITHFUL** (F3; CB1 rider)
- [x] create value transfer (debit self / credit deployee) — **FAITHFUL** (F4)
- [x] `selfdestruct` balance transfer — **NOT MODELED** (CS1, NEW)
- [x] `selfdestruct` EIP-6780 delete flag + selfdestruct set — **FAITHFUL** (F5)
- [x] precompile input framing 0x01/0x05 + 0x05–0x0a liveness — **FAITHFUL / N/A** (F6)
- [x] create2 address prediction — **OOS** (F7)

**Still NOT reached (worklist / deferred):**

- **Round-10 (DEFERRED, DL1-gated):** transient-storage (`tstore`/`tload`) slot
  allocation ORDER across a diamond (inherits DL1's DFS-vs-reverse-C3 order) +
  storage-packing re-audit against the corrected order + ctor/init order re-confirm.
  Review once the DL1 fix lands on `main`.
- **Round-12:** ABI encoder deep edges (fn-type element, tuples-in-tuples, nested
  `T[][]`/`string[]`), `encodeWithSelector`/`encodeWithSignature` dynamic edges,
  `encodeCall` type-match acceptance, `blockhash`/`blobhash` window acceptance,
  event/error deep encoding corners.
- **Memory-round-3 (M1-gated):** memory-ref alias across the call boundary + tuple
  destructure of multiple memory refs — review once the M1 fix lands.

---

## Bottom line

Round 11 read the create/create2/selfdestruct execution observables and the
precompile input framing. The deployed-contract address and success rule, the
plain-`new` and try-`new` constructor-revert bubbling, the **create** value
transfer, the **EIP-6780** selfdestruct delete flag + set, and the precompile
input framing are all **faithful** (and 0x05–0x0a have no Solidus framing surface
to diverge at all — they are source-constructed and responder-answered). The one
gap is **CS1**: `selfdestruct` records the `(from, recipient, deletesAccount)` fact
but performs no **balance transfer** — the self balance is not zeroed and the
recipient is not credited, whereas the EVM moves the balance unconditionally. It
is asymmetric with the `call`/`create` value-transfer path, which the responder
models. Reachability is UNTESTED (the witness suite asserts only the record fields
and a storage slot), so it is a modeling gap that becomes a wrong-value soundness
divergence only if the differential harness compares post-selfdestruct balances.

**NEW divergences this round: 1 (SOUNDNESS-conditional / COMPLETENESS,
reachability-UNTESTED), 0 wrong-value differentially-live.** Round-10 remains
deferred pending the DL1 fix.
</content>
