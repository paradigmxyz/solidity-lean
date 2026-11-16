# Driver tests at 800d78a9

Solar branch `alpharush/t1-driver-on-2637b` @ 800d78a98b9e64612c742d5038e7e2ec35dd52b4 (tree eff1b722c1ab2ee4a0574ff830147eca06ead23f). That commit binds the archived inputs and caveats to the fresh run. Its parent, 1844041e, holds the record's claims to its records.

| run | exit | result |
|---|---|---|
| test_generic_full: `python3 tools/certify/test_generic.py`, with SOLIDITY_LEAN_DIR at solidity-lean 44572c15 | 0 | 29 tests OK, none skipped |
| test_sh_spec: `bash tools/certify/test.sh`, with SOLAR_VERIFY set to solar-verify built at this commit (sha256 in solar-verify.sha256) | 0 | 88 ok, no FAIL, wall time 190 s. The spec cases ran. One case was skipped: foreign-solar, because the solar binary is built from this checkout. |

## Replay edge cases

`results.txt` comes from `reuse.py` and `mk.py`. They run the driver's own `replay_main` on copies of the acc4-flag replay directory, with the published fresh replay record standing in for the fresh run. No Lean runs, so these are checks only, not full replays. "old" is 1844041e and "new" is 800d78a9.

| case | 1844041e | 800d78a9 |
|---|---|---|
| control (unedited) | exit 0, CERTIFIED | exit 0, CERTIFIED |
| an archived Source.lean edited, with only its run_files digest updated | exit 0, CERTIFIED | exit 1, REJECTED: inputs/.../Source.lean |
| the gas bound in an archived shape.json edited and rehashed | exit 0, CERTIFIED | exit 1, REJECTED: inputs/.../shape.json |
| caveats emptied in both records, with certify-record.json rehashed | exit 0, CERTIFIED | exit 1, REJECTED: caveats |

## superseded/

`superseded/` holds the receipts of the same tests at 1844041e, which 800d78a9 replaces:
- test_generic_full: 25 tests OK.
- The five record-tamper cases, on 6d0f2621 ("old") and 1844041e ("new"). Each `*.old.log` and `*.new.log` is one replay. `acc4-vs-fresh.txt` checks the real acc4 record against its fresh replay.

Each `*.receipt.json` holds the command, exit code, wall time and memory peaks. Its `*.receipt.trace.tsv` holds the 2 s samples.
