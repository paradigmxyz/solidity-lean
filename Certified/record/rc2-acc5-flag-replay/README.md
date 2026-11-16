# rc2-acc5-flag-replay

Fresh-clone replay of Certified/record/rc2-acc5-flag/replay as published at
abcd096127559797224a4fdf330dd3476c65b79c (a fresh --no-checkout clone with only
Certified/record/rc2-acc5-flag checked out at that commit; it equals that tree
byte for byte) with tools/certify/certify --replay on solar driver
0479b90a422245bf77facc51ea17b960ed5c5851 (binary_commit, dirty False).

- Command: tools/certify/certify --replay /home/hand/runs/rc2-acc5-flag-replay-clone/Certified/record/rc2-acc5-flag/replay --solidity-lean /home/hand/sl445 --packages-from /home/hand/sl445 --probe-cache /home/hand/sl445 (cwd: the driver tree at 0479b90a)
- Package cache: --packages-from and --probe-cache from a solidity-lean checkout at
  44572c150176365fa5e0d56ae6c59a7a443f8122 (still replayed in full)
- Exit 0; verdict: CERTIFIED, tier certified
- Kernel replay: closure 3966, replayed 3966, trusted 0, unaccounted 0; leanchecker exit 0
- Started 2026-11-16T07:52:17Z, wall 10738.9 s; max RSS of one process 7991 MiB, peak tree RSS 8811 MiB
- Caveats (same in both runs): solidity-lean at a861b0d7a5d60d43e73337c988313f4c77675ebf, not the pinned 49d1d7f5d9b74165486bd9f634202bee1a3633eb; not end to end: solidity-lean states no source or spec theorem for flag_4ce5cf9a

## REPLAY_KEYS: 18/18 SAME

| key | record vs fresh | value (or sha256 of its JSON) |
|---|---|---|
| source.sha256 | SAME | 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d |
| spec | SAME | sha256 e5c7d88270f3e4c0 |
| options | SAME | sha256 e53b6b285a546d16 |
| functions | SAME | sha256 15699b4db07960c1 |
| environment | SAME | sha256 7b6e81fe77961a13 |
| bytecode_sha256 | SAME | f689833eb749e7509b4fb038bd8a4e251e77daa10aed088b2b12fa70ab76f69f |
| gas_bound | SAME | sha256 54c40d3465da04a1 |
| requested_tier | SAME | certified |
| solidity_lean.base | SAME | 49d1d7f5d9b74165486bd9f634202bee1a3633eb |
| solidity_lean.inputs_sha256 | SAME | sha256 d307ce0054f9f86e |
| solar.commit | SAME | 0479b90a422245bf77facc51ea17b960ed5c5851 |
| solar.binary_sha256 | SAME | 1aca58558403403bf5e3e36be83b409be7d4fc45dabf8e807c0a3335781e47c4 |
| solc.sha256 | SAME | fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| lean_toolchain.recorded_digest | SAME | 953aa1e72283c07686567bb71eeb3fca202baafe2958a7e57987d3b8c4434c25 |
| published_statement | SAME | sha256 44136fa355b3678a |
| status | SAME | CERTIFIED |
| strict | SAME | sha256 7e2e90a8229b5e71 |
| tier_reached | SAME | certified |

fresh/ is the fresh run's record directory; receipt.json, receipt.trace.tsv and
driver.log are the resource receipt and the replay driver's output.
