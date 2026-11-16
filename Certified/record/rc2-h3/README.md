# RC2 H3 (Mapping): BLOCKED, exit 3, not certified

`tests/heldout/rc-2026-11-15/Mapping/Mapping.sol` (sha256 `b39ab3912781a9b1a8cf897cf6fbb6ee7fcc98d973eb4b749195e2d773d23ccd`)
at solidity-lean `e0564a28100931a9986af9a848a57bc2bd835c67`, run once with `tools/certify/certify ... natspec` from solar `0479b90a422245bf77facc51ea17b960ed5c5851`
(binary built from that commit, binary_commit equal), solidity-lean base `49d1d7f5d9b74165486bd9f634202bee1a3633eb`,
`LEAN_NUM_THREADS=1`, requested tier certified. RC2 rerun; nothing was proved or claimed.

    BLOCKED: generic source check (2x, first myMap(address): myMap(address): source tree undefined (erasure))

`--replay` of this record exits 1 (`the record is BLOCKED: nothing to replay`). The files are byte-identical
to the run; `sha256sum -c MANIFEST.sha256` checks them.
