# acc3-succwrong: Negative control: wrong succeeds-if through the tolerant proof (set reverts above 100) (driver 5a9e6bc0)

Verdict: REJECTED: spec: set_succeeds does not check: omega could not prove the goal: (SpecConnect.lean:99)
Driver exit (strict tier exit): 1 (not certified)
Status: REJECTED
First failing stage: certify: error: spec_connect.py refuses functions of SuccWrong (above): their spec is not proved

| Field | Value |
| --- | --- |
| Driver scripts commit / tree | 5a9e6bc0e846e5f4426cff6d22476f31f638d561 / 419977aedc6fe60b92b523284185f2b3b7956475 |
| solar binary sha256 | 91d3945708fd2e11a2ee4eb8fa170502d0361bef14c792ecc13bb7ab7a4cb697 |
| solar binary built from | 5a9e6bc0e846e5f4426cff6d22476f31f638d561 (tree 419977aedc6fe60b92b523284185f2b3b7956475); Rust sources equal to the driver commit: True |
| solidity-lean base argument | 44572c150176365fa5e0d56ae6c59a7a443f8122 |
| solidity-lean executed | 0e8c8e49d1448942f73ae2e3803466957f962378 (parent 44572c150176365fa5e0d56ae6c59a7a443f8122) |
| Options | -Ogas --evm-version osaka |
| Requested tier | certified |
| Source | sha256 35a6234e6469f28c29c08fce8b92d8b59decd8b760e5ce51a55a5e2c48e1ce13 |
| Spec | natspec, sha256 35a6234e6469f28c29c08fce8b92d8b59decd8b760e5ce51a55a5e2c48e1ce13 |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| Lean toolchain | leanprover/lean4:v4.35.0 |
| Runtime bytecode sha256 | 3a2b7aa0e1e640206ff04ff7ada168ccdcc77dff3f4805d049086dfde12c6363 |
| Gas bound | 2033203 |
| Strict tier | (not reached) |
| Blocked | - |
| Replay | (not reached) |
| Host peak used memory (all processes) | 4003 MiB of 14531 |
| Resource admission | admitted (max(system_used_mib) <= mem_total_mib - 1024 and not killed for memory) |
| MIR (gen Stage0.lean) sha256 | 9088515c6bb66ade8c669bffebefbe1941eefd9b325a1760c9cb2956bc53e2c3 |
| Peak tree RSS / largest process | 7405 / 5275 MiB |
| Wall seconds | 823.0 |

Final statement: (not built)

Final check: (not reached)

Closure: (not reached)

Replay directory check (replay/ against record.json run_files): {"extra": [], "missing": [], "mismatched": []}

Files: replay/ is the driver's record directory exactly, for tools/certify/certify --replay <path>/replay:
record.json, whose run_files lists every other file in it (certify.log, inputs/, the source).
Beside it, the archival envelope: generated/ (every file of the run's Certified/<name>/ as the build saw it),
provenance.json, receipt.json with receipt.trace.tsv (every memory sample; definitions in the receipt),
driver.log, and MANIFEST.sha256, the sha256 of every file here but itself.
