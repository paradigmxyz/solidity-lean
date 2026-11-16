# H3 (Mapping): BLOCKED, not certified

Held-out case H3 of rc-2026-11-15: `tests/heldout/rc-2026-11-15/Mapping/Mapping.sol`
(sha256 `b39ab3912781a9b1a8cf897cf6fbb6ee7fcc98d973eb4b749195e2d773d23ccd`) at
solidity-lean `e0564a28100931a9986af9a848a57bc2bd835c67`, run once with
`tools/certify/certify ... natspec --contract Mapping` from solar
`800d78a98b9e64612c742d5038e7e2ec35dd52b4` on base `44572c15`, `LEAN_NUM_THREADS=1`.

Verdict: BLOCKED, exit 3. Nothing was proved or claimed.

    BLOCKED: generic source check (2x, first myMap(address): myMap(address): source tree undefined (erasure))

`get(address)` and `set(address,uint256)` agree; the public mapping getter `myMap(address)`
and `remove(address)` (`delete myMap[_addr]`) have no erased source tree. `--replay` of this
record exits 1 (`the record is BLOCKED: nothing to replay`).

The files are byte-identical to the run: `record.json` (the driver's record), `driver.log`
(stdout and stderr), `receipt.json` (command, exit, wall time, peak RSS) and `memtrace.tsv`
(2 s memory samples). `MANIFEST.sha256` covers them: `sha256sum -c MANIFEST.sha256`.
