# RC2 H4 (FunctionModifier): REJECTED, exit 1, not certified

`tests/heldout/rc-2026-11-15/draw2/H4-FunctionModifier/FunctionModifier.sol` (sha256 `3be4c2f15b9f262ff34956f9ef38e579777e00cd93423f64f3488c8716a8f4f4`)
at solidity-lean `aa9191531b28e5cd44095f8bd680f789a61729c9`, run once with `tools/certify/certify ... natspec` from solar `0479b90a422245bf77facc51ea17b960ed5c5851`
(binary built from that commit, binary_commit equal), solidity-lean base `49d1d7f5d9b74165486bd9f634202bee1a3633eb`,
`LEAN_NUM_THREADS=1`, requested tier certified. RC2 rerun; nothing was proved or claimed.

    REJECTED: certify.py cannot write the stage proofs: error: no cut points for stage0 to mir1: place-reads: a recursive call into @decrement.body

`--replay` of this record exits 1 (`the record lists no run files`). The files are byte-identical to the run;
`sha256sum -c MANIFEST.sha256` checks them.
