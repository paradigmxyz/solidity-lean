# driver: restore the helpers missing from solar #2637 head 697fc686

Solar #2637 head 697fc686 ("fix(certify): check producers' exit status and replay the whole
closure") has the driver change but not its three new files: `tools/certify/inputs.sh`,
`tools/certify/replay.py` and `tools/certify/export_check.py`. `scripts/certify` sources
`inputs.sh` at line 98, so at 697fc686 every run of the driver stops there, and `spec.sh` and the
replay step call the other two.

`restore.bundle` (sha256 24b02443cc464dfa74d86ae5a2ca8e1153dc5d36d303930df856c0790597b4a3) holds
one commit on top of 697fc686:

    0d089b13876335c3498277c7a60db25393a76092 fix(certify): add the helpers the driver sources

It adds the three files exactly as in the driver bundle (driver.bundle, bcd1ae63); nothing else
changes. `restore.patch` is the same commit as a patch.

Check: `tools/certify/test.sh` on 697fc686 + this commit, with that tree's own debug solar and
solar-verify: 88 ok, 0 fail, 1 skip (foreign-solar: the binary is built from this checkout, by
design). test.log and test.receipt.json: exit 0, 197 s wall, peak one-process RSS 1941 MiB,
peak system used 3352 MiB of 14531 MiB.

Apply:

    git fetch storm/out/driver/restore-697/restore.bundle HEAD && git merge --ff-only FETCH_HEAD
    # or: git am storm/out/driver/restore-697/restore.patch
