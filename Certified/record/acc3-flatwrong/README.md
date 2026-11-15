# acc3-flatwrong: Negative control: wrong ensures on a branchless function (clear sets 0, spec says 1) (driver 5a9e6bc0)

Verdict: REJECTED: spec: clear_meets0 does not check: omega could not prove the goal: (SpecConnect.lean:67)
Driver exit (strict tier exit): 1 (not certified)
Status: REJECTED
First failing stage: certify: error: spec_connect.py refuses functions of FlatWrong (above): their spec is not proved

| Field | Value |
| --- | --- |
| Driver scripts commit / tree | 5a9e6bc0e846e5f4426cff6d22476f31f638d561 / 419977aedc6fe60b92b523284185f2b3b7956475 |
| solar binary sha256 | 91d3945708fd2e11a2ee4eb8fa170502d0361bef14c792ecc13bb7ab7a4cb697 |
| solar binary built from | 5a9e6bc0e846e5f4426cff6d22476f31f638d561 (tree 419977aedc6fe60b92b523284185f2b3b7956475); Rust sources equal to the driver commit: True |
| solidity-lean base argument | 44572c150176365fa5e0d56ae6c59a7a443f8122 |
| solidity-lean executed | 788e31f0da0e999bbf84f987ae681d694a065291 (parent 44572c150176365fa5e0d56ae6c59a7a443f8122) |
| Options | -Ogas --evm-version osaka |
| Requested tier | certified |
| Source | sha256 853494c293c5dafce262aba9938695ad55f17354bdb76389f6a093dbabf3337c |
| Spec | natspec, sha256 853494c293c5dafce262aba9938695ad55f17354bdb76389f6a093dbabf3337c |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| Lean toolchain | leanprover/lean4:v4.35.0 |
| Runtime bytecode sha256 | cbc40a27d79f0a76003b63dbf3271c4f174325b296bb9f665f04a550538e3445 |
| Gas bound | 1502803 |
| Strict tier | (not reached) |
| Blocked | - |
| Replay | (not reached) |
| Host peak used memory (all processes) | 4022 MiB of 14531 |
| Resource admission | admitted (max(system_used_mib) <= mem_total_mib - 1024 and not killed for memory) |
| MIR (gen Stage0.lean) sha256 | eeaa871399a787add8ee6aeb9d72410b455a9663f63ccbb847e6ad1255be6b69 |
| Peak tree RSS / largest process | 7248 / 5283 MiB |
| Wall seconds | 698.9 |

Final statement: (not built)

Final check: (not reached)

Closure: (not reached)

Replay directory check (replay/ against record.json run_files): {"extra": [], "missing": [], "mismatched": []}

Files: replay/ is the driver's record directory exactly, for tools/certify/certify --replay <path>/replay:
record.json, whose run_files lists every other file in it (certify.log, inputs/, the source).
Beside it, the archival envelope: generated/ (every file of the run's Certified/<name>/ as the build saw it),
provenance.json, receipt.json with receipt.trace.tsv (every memory sample; definitions in the receipt),
driver.log, and MANIFEST.sha256, the sha256 of every file here but itself.
