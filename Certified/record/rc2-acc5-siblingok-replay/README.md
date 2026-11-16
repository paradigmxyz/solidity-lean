# rc2-acc5-siblingok-replay

Fresh-clone replay of Certified/record/rc2-acc5-siblingok/replay (published at
68e0226a9aae9cf7a3df938b79c3b9b796927e8d) with tools/certify/certify --replay on solar driver
0479b90a422245bf77facc51ea17b960ed5c5851 (binary_commit, dirty False).

- Command: tools/certify/certify --replay /home/hand/runs/rc2-acc5-siblingok-replay-clone/Certified/record/rc2-acc5-siblingok/replay --solidity-lean /home/hand/sl445 --packages-from /home/hand/sl445 --probe-cache /home/hand/sl445 (cwd: the driver tree at 0479b90a)
- Package cache: --packages-from and --probe-cache from a solidity-lean checkout at
  44572c150176365fa5e0d56ae6c59a7a443f8122 (still replayed in full)
- Exit 0; verdict: CERTIFIED, tier certified
- Kernel replay: closure 3970, replayed 3970, trusted 0, unaccounted 0; leanchecker exit 0
- Started 2026-11-16T13:52:33Z, wall 11355.8 s; max RSS of one process 7990 MiB, peak tree RSS 8812 MiB
- Caveats (same in both runs): solidity-lean at 63f4b121daaebf8a1eac7b09285ef0082d3b69cb, not the pinned 49d1d7f5d9b74165486bd9f634202bee1a3633eb; not end to end: solidity-lean states no source or spec theorem for siblingok_e3749c22

## REPLAY_KEYS: 18/18 SAME

| key | record vs fresh | value (or sha256 of its JSON) |
|---|---|---|
| source.sha256 | SAME | e3749c22494d07461b2074268882227824a84765f8afc21de6bf4da56a61ca47 |
| spec | SAME | sha256 2c7e6981e1e9c17f |
| options | SAME | sha256 e53b6b285a546d16 |
| functions | SAME | sha256 89025d3a9bcc77c0 |
| environment | SAME | sha256 7b6e81fe77961a13 |
| bytecode_sha256 | SAME | 707f63a7b096952969a5361289b6a3750ca33ebf6bc955b77d10276506baa0de |
| gas_bound | SAME | sha256 fb5893da92da9d81 |
| requested_tier | SAME | certified |
| solidity_lean.base | SAME | 49d1d7f5d9b74165486bd9f634202bee1a3633eb |
| solidity_lean.inputs_sha256 | SAME | sha256 8c6e8d22e5ac6d88 |
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
