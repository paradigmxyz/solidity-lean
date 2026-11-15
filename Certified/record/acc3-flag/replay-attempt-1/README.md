# Fresh-clone --replay of acc3-flag/replay (published at 039ef8bd)

Command (solar driver 5a9e6bc0, from a git clone of alpharush/t1-generic-records at 039ef8bd):

    tools/certify/certify --replay <clone>/Certified/record/acc3-flag/replay --solidity-lean ~/sl445 --packages-from ~/sl445 --probe-cache ~/sl445

Result: exit 1, REJECTED: replay: solidity_lean.inputs_sha256 differs between the record and the fresh run.
The fresh run itself reached CERTIFIED (strict exit 0; fresh-record/record.json), but one pinned input differs:
Certified/flag_4ce5cf9a/Source.lean, whose importedSourceName is the absolute path the front end read the
source from (record: /home/hand/acc-src/Flag.sol; replay: the clone's replay/Flag.sol). See Source.lean.diff.
The record is therefore not reproducible from another directory, and acc3-flag is not accepted.
Fix: solar 6d0f2621 reads the source from a path fixed by its digest; acc4-flag reruns Flag on it, then the
same fresh-clone replay.
