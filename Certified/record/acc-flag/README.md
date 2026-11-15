# acc-flag: T5 held-out positive Flag; rejected on driver 20a27f39 by a driver gap in Shape.lean (fixed in c167421c, rerun as acc2-flag)

Verdict: REJECTED: scripts/certify: exits 1: -- | error: build failed | certify: error: flag_4ce5cf9a.Final does not check (flag_4ce5cf9a.Shape): the proof is not of the published statement
Driver exit (strict tier exit): 1 (not certified)
Status: REJECTED

| Field | Value |
| --- | --- |
| Driver (solar) commit | 20a27f39685284bea5a0fe40a7fed0437cfcf694 (dirty: False) |
| solar binary sha256 | 8243e8dc99444c0840a436f1825d75374d891a779a956f6eeb82125e80bbb5d9 (solar 0.3.0-dev+commit.abe16b2e) |
| solidity-lean base | 44572c150176365fa5e0d56ae6c59a7a443f8122 |
| solidity-lean inputs commit | 3927e703b2a79c66d6803f21c201d3dcd9b5f255 |
| Options | -Ogas --evm-version osaka |
| Requested tier | certified |
| Source | Flag.sol, sha256 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d |
| Spec | natspec, sha256 4ce5cf9a87520dc956a1e7366d5f646a07739832e44a3d8dec2eb656deb6388d |
| solc | 0.8.35, sha256 fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4 |
| Lean toolchain | leanprover/lean4:v4.35.0 |
| Runtime bytecode sha256 | f689833eb749e7509b4fb038bd8a4e251e77daa10aed088b2b12fa70ab76f69f |
| Gas bound | 3580203 |
| Strict tier | (not reached) |
| Blocked | - |
| Wall seconds / peak tree RSS MiB | 1476.5 / 8789 |

Final statement: (not built)

Final check: (not reached)

Closure: (not reached)

Files: record.json (with run_files, the manifest of every other file here), certify.log, inputs/,
receipt.json (command, exit code, wall time, memory), driver.log. This README is not in the manifest.
