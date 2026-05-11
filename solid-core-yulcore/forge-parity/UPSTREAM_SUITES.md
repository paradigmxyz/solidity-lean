# Upstream Foundry Suite Plan

The long-term target is to run large Foundry test suites twice: once with
Foundry/revm as the oracle and once through the Lean EVM runner. The corpus
manifest is `foundry-suites.toml`; checkouts live under `.foundry-suites/` and
are intentionally not committed.

## Commands

List pinned suites:

```sh
python3 scripts/foundry_corpus.py list
```

Fetch a pinned upstream suite:

```sh
python3 scripts/foundry_corpus.py fetch --suite solmate
```

Scan for `vm.*` cheatcode calls:

```sh
python3 scripts/foundry_corpus.py scan --suite solmate
```

Run ordinary Foundry for an enabled or selected suite:

```sh
python3 scripts/foundry_corpus.py forge --suite local-forge-parity -- --list
```

## Lean Replay Milestones

1. Import `forge build` artifacts and enumerate test functions.
2. Deploy the test contract, run `setUp()`, then run one test function in a
   persistent per-test chain state.
3. Intercept the Foundry cheatcode address in Lean as a special external call.
   This is now active for the first deterministic replay tier.
4. Implement the first cheatcode tier: `deal`, `etch`, `store`, `load`, `prank`,
   `startPrank`, `stopPrank`, `warp`, `roll`, block/env setters, access-list
   warm/cool helpers, `recordLogs`, `getRecordedLogs`, `snapshotState`, and
   `revertToState`. `expectRevert` is modeled for child calls; `expectEmit`,
   `expectCall`, and `label` are currently permissive no-ops so suites can be
   replayed before assertion-checking is modeled.
5. Compare status, returndata, logs, storage/account state, balances, nonces,
   deployed code, and gas when the test is deterministic and gas assertions are
   meaningful.
6. Flip upstream suites from `lean_replay = "planned"` to active only when the
   runner can execute their setup/test lifecycle without source edits.

Forked tests, filesystem/FFI cheatcodes, RPC-dependent tests, and fuzz or
invariant campaigns should stay out of the required pass set until deterministic
unit-test replay is stable.

## Current Upstream Signal

`solmate` is fetched locally and currently scans as 568 `test*`/`invariant*`
functions with 110 `vm.*` calls. Its eight unique cheatcodes are now covered by
the replay tier: `prank`, `expectRevert`, `warp`, `store`, `assume`, `load`,
`addr`, and `sign`. The cryptographic identity cheatcodes are modeled by
explicit host-oracle inputs populated by the replay runner with `cast wallet`,
so the Lean EVM core stays deterministic and crypto-free.
