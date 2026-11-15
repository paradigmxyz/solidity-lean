# skim(address) (uv2_sk): work in progress, 05:45 UTC Nov 15

Same base and script as RESULT.md (solidity-lean f8a4a744 + patches 0001–0004, solar 902cccc2 + scoped-dispatcher fix). Nothing in this file is a finished claim.

## Checked so far (receipts-uv2_sk.log)
- Mir1–Mir4: exit 0 (79–578 s, ≤4.8 GB).
- Evm1–Evm19: exit 0 (88–157 s, ≤2.8 GB). These were built before the `cond_slt` lemmas below. They will be rebuilt in the final run.
- No axiom audit yet.

## Stack scheduling (Sched): open
1. **One segment.** Stopped by hand after 75 min at 9.7 GB, still growing on a 14 GB machine (receipts-uv2_sk.log, run killed).
2. **Cut block by block.** This uses `wip-solar-scoped-loop-check.patch`, which checks only loops a call in scope reaches; mint()'s sqrt loop otherwise blocks every cut. 16 of 17 segments check in 3–20 s (receipts-uv2_sk-probes.log). The exception is skim's bb5→bb2→bb7 path, which runs `sub`, `_safeTransfer` (an external CALL and return-data checks) and a STATICCALL with no cut: it times out at 100M heartbeats. No cut is placed in skim's blocks 2/7 or in the callees, because the ADDRESS value (v17) is live there and the scheduler recomputes it instead of keeping it on the stack.
3. **Call-constant relations.** `wip-solar-call-constant-cuts.patch`: a cut relates a value read by ADDRESS, CALLDATASIZE or CALLVALUE that the stack doesn't hold through a condition `env v = <its word>`. With it, skim's blocks get cuts. But segments that end at cuts inside `sub`/`_safeTransfer` fail: the MIR side runs past the callee cut where the EVM side stops. The cause is not yet understood. With callee cuts turned off (cuts only in skim's own blocks), the bb7 segment runs 748 s at 30M heartbeats and leaves 6 leaves. One of those leaves is infeasible: it holds both `slt RDS 32 = 0` and `sgt 32 RDS ≠ 0` (the return data size checks), and the procedure has no lemma for signed comparisons.
4. **Signed comparisons.** `wip-tactic-cond-slt.patch` adds `cond_slt`/`cond_sgt` (and their zero-first forms) to the procedure's simp set. Re-probing skim's bb7/bb8 segments with it is running.

Next: finish Sched (step 4), then rerun all three scopes (getReserves, sync, skim) from the script with the final tactic, because a simp-set change can affect the earlier proofs. Then audit and push.
