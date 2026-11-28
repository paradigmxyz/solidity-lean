# SiblingLeak against the certified SiblingOk

SiblingLeak (`tests/heldout/negative/SiblingLeak.sol`, sha256 7e2f4c33) states `x <= 5 ==> level == 1`, which is false on the else-branch. It can be proved only if the then-branch's `x > 5` leaks into its sibling. Its control, SiblingOk, was certified (strict exit 0) on the same pins: solar driver 0479b90a and solidity-lean base 49d1d7f5, with the solar binary built from 0479b90a, `-Ogas`/osaka.

Result: one full run, exit 1, after 868 s:

    REJECTED: spec: set_meets0 does not check: omega could not prove the goal: (SpecConnect.lean:67)

The spec connection for `set(uint256)` does not check. The `set_holds` and `set_holds_in` theorems in the failed variant depend on `sorryAx`, which the axiom gate reports as a difference from the allowed set. The record's status is REJECTED. Peak tree RSS was 6159 MiB, the largest process 5278 MiB, and peak system use 3994 of 14531 MiB (`receipt.json`, with a 2 s trace in `receipt.trace.tsv`). Command: `leak.sh`.
