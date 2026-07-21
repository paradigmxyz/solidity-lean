# Fix-time dedup via differential replay

## The problem with dedup at submission time

A divergence-finding arena must avoid counting one underlying engine defect twice. The
submission-time layer dedups by **fingerprint matching** (`known_gaps.py` v2:
`match_submission` computes a canonical, rename/reorder-invariant structural hash of
the submission's sources and matches it against the registry's repro-DERIVED keys).
That exact-match layer is deliberately conservative: it catches a copy/re-skin of a
*published* repro, but a **re-skinned** known gap expressed as a *different program*
— rename the feature, reword the contract, wrap a revert reason in
`abi.encodePacked` — still dodges it ("novelty inflation"). The advisory
`feature_hint` / `delta_cluster_hint` (keyed on the curated slug and the
*adjudicator-derived* `(component, delta_shape)`) surface candidates, but they are
advisory only (never set `duplicate_of`, never change `qualifies`) because they
over-cluster distinct bugs.

Same-**root-cause** dedup at submission time is effectively undecidable: "are these
the same bug?" means "do they share a root cause", which means understanding the
bug — manual, and defeated by re-skinning.

## The key: "does the same fix kill both?"

The dedup key that actually matters is **"does the same fix kill both?"** — and that
*is* computable, just not at submission time. Defer it to **fix time**, where it
becomes an exact, engine-derived, nearly-free oracle:

- `E0` = the current solidity-lean (carries all the known gaps).
- `E1` = a **reference build** = `E0` + fixes for the known gaps (G1..G22).
- Re-run a qualifying submission against `E1`:
  - divergence **vanishes** under `E1` → covered by a known-gap fix → **DUPLICATE**.
  - divergence **persists** under `E1` → not covered → genuinely **NOVEL**.

This keys on **engine-behavior-under-patch**, not on anything the submitter controls,
so it is immune to re-skinning. The EVM observable is engine-independent (it is the
measured ground truth), so replaying only re-runs the **solidity-lean** side and
re-compares against the same EVM observable.

For dedup **among fresh novel submissions** (no known fix yet): admit all, and when
the first novel bug is fixed, re-run the other still-open novel submissions against the
newly-patched engine; every one that vanishes was a duplicate of that fix → collapses
into one distinct-finding class whose representative is the earliest submission
(`collapse_classes`).

## Operational flow

1. Adjudicate normally; admit everything that qualifies.
2. When a maintainer fixes a gap (which they do anyway), the patched engine becomes a
   new reference `E1`.
3. Replay all still-open admitted submissions against `E1`
   (`replay_against_reference`). `DUPLICATE`s collapse onto that fix; `NOVEL`s remain.
4. Each surviving `NOVEL` class counts as one distinct finding, represented by its
   earliest submission; the rest are folded in as duplicates.
5. `SHIFTED` / `INCONCLUSIVE` go to human review (rare).

Residual manual work shrinks to (a) producing the fix — done regardless — and (b) the
rare judgment call where one fix arguably covers two distinct root causes.

## API (`contest/dedup_replay.py`)

- `classify_dedup(e0_report, e1_report) -> DedupVerdict` — the pure classifier
  (`NOVEL` / `DUPLICATE` / `SHIFTED` / `INCONCLUSIVE` / `NOT_IN_POOL`).
- `collapse_classes(items) -> [UniqueClass]` — re-skins of one novel defect collapse
  into one distinct-finding class (represented by its earliest member); duplicates
  collapse away.
- `replay_against_reference(sample, reference_repo, ...)` — runs `adjudicate` against
  `E0` (default build) and `E1` (`tools=ToolPaths(repo=reference)`), then classifies.
  `adjudicate_fn` / `tool_factory` are injectable so the logic is unit-tested without
  a second Lean build (see `run_samples.dedup_replay_unit_tests`).
- CLI: `python -m contest.dedup_replay <submission> --reference-build <E1>`.

Producing the actual gap-fixes lives in `SolidCore/**` and is out of scope for this
module.

## End-to-end demonstration (round 29, real Lean builds)

A worktree build was patched with a DEMO-ONLY injected gap — `SolidCore`
`RevertData.overflow` set to `panic 0x99` instead of `0x11` (never merged) — so the
`panic_overflow` sample diverges from EVM under it. Adjudicated and replayed via
`contest/demo_dedup_replay.py`:

```
Adjudicating panic_overflow against E0 (buggy build, panic 0x99)...
  E0 verdict: SOUNDNESS_GAP  qualifies=True  fp=revert_data|checked-overflow-panic|wrong-panic
  solidity-lean=revert|panic:153##EVT####STO##  evm=revert|panic:17##EVT####STO##

Replaying against FIXED reference (main, panic 0x11)...
  E1(fixed) verdict: NO_DIVERGENCE  qualifies=False        -> DUPLICATE

Replaying against SAME (still-buggy) reference...
  E1(same) verdict: SOUNDNESS_GAP  qualifies=True           -> NOVEL
```

Both branches classify correctly against actual differing engine builds: a reference
that fixes the overflow panic code collapses the submission to `DUPLICATE`; a
reference that still emits the wrong code keeps it `NOVEL`.
