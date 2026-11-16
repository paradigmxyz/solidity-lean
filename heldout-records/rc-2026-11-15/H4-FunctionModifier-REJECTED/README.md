# H4 (FunctionModifier): REJECTED, exit 1, not certified

Held-out case H4 of the second draw: `tests/heldout/rc-2026-11-15/draw2/H4-FunctionModifier/FunctionModifier.sol`
(sha256 `3be4c2f15b9f262ff34956f9ef38e579777e00cd93423f64f3488c8716a8f4f4`) at solidity-lean
`aa9191531b28e5cd44095f8bd680f789a61729c9`, run once with `tools/certify/certify ... natspec --contract FunctionModifier`
from solar `800d78a98b9e64612c742d5038e7e2ec35dd52b4` (binary built from that commit) on base `44572c15`,
`LEAN_NUM_THREADS=1`, requested tier certified.

Verdict: REJECTED, exit 1. Nothing was proved or claimed.

    REJECTED: certify.py cannot write the stage proofs: error: no cut points for stage0 to mir1: place-reads: a recursive call into @decrement.body

The run stopped after the source and bytecode envelope checks, at the gas bound, before the probe and
any proof. `--replay` of this record exits 1 (`the record lists no run files`).

The files are byte-identical to the run: `record.json`, `driver.log`, `receipt.json` and `memtrace.tsv`.
`MANIFEST.sha256` covers them: `sha256sum -c MANIFEST.sha256`.
