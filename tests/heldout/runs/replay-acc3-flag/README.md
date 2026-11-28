# Replay mutations against acc3-flag

Target: `Certified/record/acc3-flag/replay/` on solidity-lean `alpharush/t1-generic-records` @
039ef8bd. That is Flag, CERTIFIED at strict exit 0 on solar 5a9e6bc0 with solidity-lean base 44572c15.
Driver: solar 5a9e6bc0e846e5f4426cff6d22476f31f638d561, with `tools/certify/generic.py`'s
`replay_main`. The driver's hash and tree are recorded in each table, unchanged across the cases.

Command (from the driver's checkout):

    python3 scripts/verify/mutant/generic/negatives.py --replay-from <record>/replay \
      --replay 'tools/certify/certify --replay {dir} --solidity-lean <solidity-lean checkout> --work {work}' \
      --layer file --no-fresh-run --work <work> --table <work>/table.md

* `file/`: the nine cases with one run file edited. Each case's log (the command and the driver's
  output), `receipts.json` (command, exit, verdict line, UTC start and end, sha256 of the log) and
  the table. All nine are refused at the manifest with exit 1, and no build starts.
* `pin-pre/`: from `--layer pin --no-fresh-run`, the pin case the driver refuses before its fresh
  run (stale-source: record.json source.sha256). The other eight pin cases pass the manifest. They
  wait for the driver's fresh cold run and run serially later.

Control: an unedited copy passes the manifest and reaches `== replay:` (the fresh cold run's
command). It was stopped there.

