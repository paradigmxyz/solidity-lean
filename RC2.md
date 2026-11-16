# Release candidate 2 (2026-11-16)

Status: **OPEN: 2 of 4 held-out verdicts in, 0 certified.** H3 BLOCKED, H4 REJECTED (the second
draw stays 0/1); H1 and H2 pending. Publisher: the acceptance reviewer (Lane 6), the only publisher of
RC artifacts; one commit per update on `alpharush/rc-2026-11-16`. The first candidate, at driver
800d78a9, stays frozen in `RC.md` as a negative report (0/3 original held-out, 0/1 second draw) and is
history here: nothing in RC2 changes its verdicts.

## Pins

| What | Pin |
|---|---|
| RC2 driver (solar) | `alpharush/t6-getter-fix` @ 0479b90a422245bf77facc51ea17b960ed5c5851. Chain: 800d78a9 → bb626f8a (UTF-8 cut fix: `final_neg.sh`, `generic.py`, `test_generic.py`) → 0479b90a (only `tools/certify/solidity-lean.rev` → 49d1d7f5) |
| solidity-lean base | 49d1d7f5d9b74165486bd9f634202bee1a3633eb (one commit on 44572c15: "fix(spec): read a returned word back in tree_meets"; `Verify/Spec/Tree.lean`, new `Verify/Spec/TreeReturnCheck.lean`, `lakefile.lean`) |
| Held-out set | original draw H1-H3: `alpharush/rc-heldout` @ e0564a28100931a9986af9a848a57bc2bd835c67 (frozen procedure); second draw H4: aa9191531b28e5cd44095f8bd680f789a61729c9 (`draw2/`, closed at H4) |
| Driver test receipts | as reported by T6: `test.sh` exit 0, 88 ok; `test_generic` 32 passed, 1 skipped. Not rerun by the reviewer |

## Run contract (unchanged from RC1)

- The frozen held-out procedure, set e0564a28: one full run per case, no edits to cases, driver or base.
- Record under `Certified/record/rc2-<case>/` with a `MANIFEST.sha256`; report exit, tier reached,
  wall time, peak RSS and the record's commit.
- **Exact-pin rule:** a case is accepted only with certify exit 0 **and** a fresh-clone `--replay` on
  the same driver 0479b90a with all 18 `REPLAY_KEYS` SAME. A replay on any other sha is a
  compatibility check only.
- Tracked keepalive. A run killed by a Hand pause is recorded as **ABORTED** and restarted once; both
  are reported.

## Held-out verdicts

| Draw | Case | Runner | Verdict | Tier | Wall / peak RSS | Record | Replay (exact-pin) |
|---|---|---|---|---|---|---|---|
| original (denominator 3) | H1 SimpleStorage | T6 | pending | | | | |
| original | H2 ViewAndPure | T7 | pending | | | | |
| original | H3 Mapping | T8 | **BLOCKED** (exit 3): generic source check, `myMap(address)` and `remove(address)`: source tree undefined (erasure) | none | 238.5 s / 2.93 GB tree RSS | [`Certified/record/rc2-h3/`](https://github.com/paradigmxyz/solidity-lean/tree/bf8b8a6ed41837f9a1b881262ccbcbeb443d1350/Certified/record/rc2-h3) | n/a: `--replay` exits 1 (BLOCKED, nothing to replay) |
| second (denominator 1, closed) | H4 FunctionModifier | T8 | **REJECTED** (exit 1): no cut points for stage0 to mir1, a recursive call into `@decrement.body` | none | 2.1 s / below the 2 s sampler | [`Certified/record/rc2-h4/`](https://github.com/paradigmxyz/solidity-lean/tree/bf8b8a6ed41837f9a1b881262ccbcbeb443d1350/Certified/record/rc2-h4) | n/a: `--replay` exits 1 (no run files) |

RC1 verdicts at 800d78a9, for comparison only: H1 REJECTED (spec step, `get_meets0`), H2 REJECTED
(resource; spec step times out), H3 BLOCKED (mapping getter and `delete` erasure), H4 REJECTED
(recursion). RC2's base targets H1's returned-word gap; the others are not expected to change unless a
fix for them is in the pin.

## Other records

| Record | Runner | Driver | Verdict | Replay | Accepted |
|---|---|---|---|---|---|
| acc5 | T1 | 0479b90a | pending | pending | pending |

## Addenda carried over (not RC2 verdicts)

- **Counter source-consumer edge** (from RC1 addendum A1): T4 `alpharush/t4-loopvc-rc` @
  e13cda49ed806cd3d35937ae8d9f26cfe357a800 (replayed 675964cc), receipt 34/34, exit 0: the
  expected-type edge for **source semantics only**. Caveats: `replay.sh` builds `Receipt` with
  linked packages (not a full `leanchecker` closure replay); the resource wrapper reads
  `RUSAGE_CHILDREN.ru_maxrss` (largest child, not the whole process tree); the module manifest
  leaves out the transitive source model; not hermetic, no aggregate resource admission, no
  end-to-end claim; compiler solar fd53f637, not the RC2 driver.
- **E6 any-caller over fresh bytes:** T2 `alpharush/t2-e6-transfer-any-caller` @
  52152f589b310142f8c807c429545ddfc5f37c64 (parent b0196e92), "transfer from every caller over fresh
  bytes". **Pending its closure replay**; not reviewed here yet, and not part of any RC2 verdict.

## Open gaps

- `id(x)`-style returns: a function returning a word (H1's gap) is targeted by base 49d1d7f5; OPEN
  until a held-out case certifies with an exact-pin replay.
- Mapping: the compiler-generated getter of a `public` mapping and `delete` of an element (H3).
- Recursion (H4): admitted by `envelope()`, refused at the gas-need step.
- Constructor / deployment / lifecycle: no tier offered.
- Any caller beyond the fixed one (0x2000) in the generic driver; E6 above is pending.
- Loops at MIR, bytes and gas (source-level Counter edge only).
- Pair: BLOCKED.

## Receipts

Filled in as verdicts land, each with its record commit and a link.

- **R1, H3 and H4 (T8).** Runner commit [bf8b8a6e](https://github.com/paradigmxyz/solidity-lean/commit/bf8b8a6ed41837f9a1b881262ccbcbeb443d1350) on `alpharush/heldout-rc2-h3-h4` (parent 49d1d7f5); `Certified/record/rc2-h3/` and
  `rc2-h4/` are copied here byte for byte. Checked by the reviewer: both `MANIFEST.sha256` pass
  (manifest sha256 a0d3f1c5… and 9d8f203d…; record.json 7e7a4bcf… and 845680da…); `solar.commit`
  and `binary_commit` are 0479b90a, `dirty: false`; source sha256 b39ab391… equals `Mapping.sol` at
  e0564a28 and 3be4c2f1… equals `draw2/H4-FunctionModifier/FunctionModifier.sol` at aa919153;
  `bytecode_sha256` equals the RC1 records (90714756… and fe2739e8…). Rerun on a 0479b90a checkout:
  `--replay` exits 1 on both records with the messages above, and `--tier lifecycle` exits 2 (tier
  not offered). Wall time and peak RSS come from each run's `receipt.json` (`LEAN_NUM_THREADS=1`,
  tracked keepalive, no Hand pause, no ABORTED run). Caveats: `record.json` does not name the
  solidity-lean commit, so base 49d1d7f5 is the runner's statement (README); each record's
  `MANIFEST.sha256` leaves out its README, which `RC2.MANIFEST.sha256` covers. The pin does not
  change either RC1 verdict: H3's mapping getter and `delete` gap and H4's recursion gap stay open.

## Files

- `RC.md`: the frozen RC1 report (800d78a9), unchanged from b83d7526.
- `RC2.md`: this file. `RC2.MANIFEST.sha256` covers this file and every file under
  `Certified/record/rc2-*`.
- `Certified/record/rc2-h3/`, `Certified/record/rc2-h4/`: T8's records, byte-identical to bf8b8a6e.
