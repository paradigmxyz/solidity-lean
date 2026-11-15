# acc-flag: T5 held-out positive Flag; rejected on driver 20a27f39 by a gap in the generated Shape.lean (fixed in c167421c, rerun as acc2-flag)

Verdict: REJECTED: scripts/certify: exits 1: -- | error: build failed | certify: error: flag_4ce5cf9a.Final does not check (flag_4ce5cf9a.Shape): the proof is not of the published statement
Driver exit (strict tier exit): 1 (not certified)
Status: REJECTED
First failing stage: flag_4ce5cf9a.Final: error: Certified/flag_4ce5cf9a/Shape.lean:128:4: unsolved goals

| Field | Value |
| --- | --- |
| Driver scripts commit / tree | 20a27f39685284bea5a0fe40a7fed0437cfcf694 / 4904ff637c346c81e0bd2f6d858411c264c0aca3 |
| solar binary sha256 | 8243e8dc99444c0840a436f1825d75374d891a779a956f6eeb82125e80bbb5d9 |
| solar binary built from | abe16b2ea8648505fda4d2f40416c748bd21a931 (tree defe9f13eeefd078ddfa18e12b0211eec0edd5f6); Rust sources equal to the driver commit: True |
| solidity-lean base argument | 44572c150176365fa5e0d56ae6c59a7a443f8122 |
| solidity-lean executed | 3927e703b2a79c66d6803f21c201d3dcd9b5f255 (parent 44572c150176365fa5e0d56ae6c59a7a443f8122) |
| Options | -Ogas --evm-version osaka |
| Requested tier | certified |
| Source | sha256 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d |
| Spec | natspec, sha256 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| Lean toolchain | leanprover/lean4:v4.35.0 |
| Runtime bytecode sha256 | f689833eb749e7509b4fb038bd8a4e251e77daa10aed088b2b12fa70ab76f69f |
| Gas bound | 3580203 |
| Strict tier | (not reached) |
| Blocked | - |
| Replay | (not reached) |
| Host peak used memory (all processes) | 3990 MiB of 14531 |
| Peak tree RSS / largest process | 8789 / 5286 MiB |
| Wall seconds | 1476.5 |

Final statement: (not built)

Final check: (not reached)

Closure: (not reached)

Files: record.json (its run_files lists the driver's own files), certify.log, inputs/ (what the driver
committed before the proof run), generated/ (every file of the run's Certified/<name>/ as the build saw it),
provenance.json, receipt.json, driver.log, and MANIFEST.sha256, the sha256 of every file here but itself.
