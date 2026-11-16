# Byte provenance of this packet

The driver hashes files as raw bytes (`sha256_file` reads `read_bytes()`; no path or timestamp
normalization). `record/record.json` `run_files["certify.log"]` = `a5df9454…` is the hash of
`certify.log` as the driver wrote it, and that file on the run host still hashes to it.

The committed `record/certify.log` (`16820861…`), `record/record.json`, outer `certify.log`
(`cd413d7b…`) and `receipt.json` differ from the originals for one reason: before committing,
every absolute home path `/home/hand/` was rewritten to `~/` (two lines in `record/certify.log`,
18 bytes shorter: 12021 to 12003). Nothing was truncated or otherwise edited. The originals contain
no `~/`, so reversing the rewrite reproduces them byte for byte:

    bash tests/heldout/runs/rc2-siblingleak/check-manifest.sh

checks every row of `MANIFEST.tsv`. The other `run_files` entries (`SiblingLeak.sol` and the
`inputs/` files) were not archived; on the run host each still matches its hash in
`record/record.json`. `leak.sh` and `README.md` are harness files, not driver output, and are not
in the manifest.

The verdict is unchanged: exit 1, `REJECTED: spec: set_meets0 does not check`.
