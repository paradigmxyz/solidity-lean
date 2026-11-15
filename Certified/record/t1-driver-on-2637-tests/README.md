# Driver tests on the reconciled certify driver

Solar branch "alpharush/t1-driver-on-2637b", commit c09510a39b5c9940845d2c19928c742f676b8675
(tree c9697d98fa3000fb2fe0484c7cc41c0b7c956cc6, parent 6cba89f5aac46f5edf85c4d0f9b174297b841f73, the
head of "alpharush/certified"). The tests ran on a local commit with the same tree (env.txt).

| run | command | exit | result |
|---|---|---|---|
| test_generic | python3 tools/certify/test_generic.py | 0 | 20 tests, OK, 1 skipped (needs SOLIDITY_LEAN_DIR) |
| test_generic_full | same, with SOLIDITY_LEAN_DIR set to a solidity-lean checkout at 44572c15 | 0 | 20 tests, OK, none skipped |
| test_sh | bash tools/certify/test.sh, Lean 4.35.0 on PATH | 0 | all passed; the spec case skipped (SOLAR_VERIFY not set) |

Each *.receipt.json holds the command, exit code, wall time and memory peaks; its
*.receipt.trace.tsv holds every 2 s sample (unix time, system_used_mib, tree_rss_mib).
