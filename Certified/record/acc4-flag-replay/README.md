# acc4-flag fresh-clone replay

This directory is the result of replaying the published record `Certified/record/acc4-flag/replay` from commit d66e60bf7d303ddb077246bdc7336300fc22a279. The replay used a fresh clone and a cold run.

- Command: `tools/certify/certify --replay <clone>/Certified/record/acc4-flag/replay --solidity-lean <44572c15 checkout> --packages-from <same> --probe-cache <same>`
- Driver: solar 6d0f2621693c2c4939eaf6241406a1674b22419c. The solar binary was built by the driver from that commit, with sha256 62c9d6edaecd117a8f2fb98dbf6b59800f75ee1e055e99957cc85adbebf5870f.
- solidity-lean base: 44572c150176365fa5e0d56ae6c59a7a443f8122.
- Verdict: `CERTIFIED: replay ... every pin reproduced by a fresh cold run`, driver exit 0, wall time 8620.6 s.
- REPLAY_KEYS: all 18 are identical, including solidity_lean.inputs_sha256 (see replay-keys.txt).
- Strict result: tier certified, holds=true. Every component is true: published_statement, equivalence, termination, resources, source_bound, provenance_clean, replay_full, spec and strongest.
- Final theorem: Certified.flag_4ce5cf9a.Final.final : Certified.flag_4ce5cf9a.Final.Statement, shape SolidCore.Verify.Generic.Expected. Its axioms are propext, Classical.choice and Quot.sound.
- Closure: 3966 modules replayed out of 3966, trusted 0, unaccounted [].
- Resources (rep4-flag.receipt.json, raw trace rep4-flag.receipt.trace.tsv, sampled every 2 s, 4303 samples): peak machine-wide used memory 10266 MiB (MemTotal - MemAvailable), peak process-tree RSS 12338 MiB, largest single process 11789 MiB, MemTotal 14531 MiB.
- Caveats carried from the record:
  - The record's caveat names solidity-lean.rev (d0ab5d63), which predates this base.
  - The fields "published_statement {}" and "states no source or spec theorem" are legacy fields copied from scripts/certify. The strict published_statement component is computed from the Final theorem instead. Driver 896493b5 records the Final theorem in published_statement and is not applied to this replay.
  - The environment is fixed: caller 0x2000, contract at 0x1000. It does not cover any caller.

fresh-run/ is the replay's own record directory. MANIFEST.sha256 covers every file in this directory.
