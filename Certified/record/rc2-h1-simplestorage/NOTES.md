# Held-out H1 (SimpleStorage), RC2 pin: ABORTED-env (driver exit 1)

Label: ABORTED-env (STATUS.json). Cache preparation: the --packages-from cache was missing the oleans of SolidCore.Refinement.Statement's closure, and the driver mounts packages read-only. This is not an H1 verdict. superseded_by: pending (a full rerun on the same driver and base after the cache is completed outside the driver). Exit 1 and every log below are kept as the driver wrote them.

- Case: tests/heldout/rc-2026-11-15/SimpleStorage/SimpleStorage.sol --contract SimpleStorage, held-out set e0564a28 (source sha256 928cc1594907cb4d56183be7565db8b60bee77c2ffc9fc731083bf31dc1bc082). One full run, no reuse.
- Driver: solar 0479b90a422245bf77facc51ea17b960ed5c5851 (tree e87de2594c4500a8cc5cd11a0a6703cf460d8da3, clean), solidity-lean base 49d1d7f5d9b74165486bd9f634202bee1a3633eb, solc 0.8.35, Lean v4.35.0. See PINS.json.
- Command: record.json "command" (natspec spec, default requested tier certified, --packages-from/--probe-cache a solidity-lean checkout's prebuilt package cache).
- Verdict: REJECTED, exit 1. requested_tier certified; no tier reached (the record has no statuses).
- Stages passed: 1-5 (compile, stage proofs, audit of 26 theorems: propext, Classical.choice, Quot.sound only), 6 (spec export whole; "spec connected generically: set_holds get_holds").
- Stage failed: 6b, the published statement: "simplestorage_928cc159.Statement does not check". Its build (lake-build.log) failed only on 9 EthLib modules (EthLib.Execution.Proofs.*, EthLib.Base.Proofs.MapM) that SolidCore.Refinement.Statement imports and that were not built in the --packages-from cache: lake had to build them inside the driver's read-only package mount and stopped with "failed to remove output artifacts: read-only file system (error code: 30)". No Lean proof error appears in the log.
- The cache was prepared on this machine by 'lake exe cache get' and 'lake build SolarTV' at the earlier base; that closure does not include those EthLib proof modules. The earlier H1 run (driver 800d78a9) stopped in stage 6 and never reached 6b, so it never needed them.
- bytecode_sha256 6e95f821ecc2c71682bb59cd089429e0ab967f2cb33da8a32ffbce7135e9d402. Envelope: source inside (get(), num(), set(uint256)); bytecode has no call, creation, gas or return-data opcode; gas bound 1944803. Probe: typecheck ok; constructor returns; storage []; get(), num(), set(uint256) agree.
- Wall 4309.7 s (driver 04:48:34Z to 06:00:24Z, 2026-11-16 UTC); peak RSS: largest process 5277 MB, process tree 6180 MB (slot-receipt.json); LEAN_NUM_THREADS=1.
- Lifecycle tier: '--tier lifecycle' on the same driver is a usage error (tier not offered), exit 2 (lifecycle-tier.log).
- No replay and no tampered-claim replay: there is no certified record.

Files: driver.log, certify.log, lake-build.log (scripts/certify's Lean build log), record.json, inputs/, SimpleStorage.sol, PINS.json, slot-receipt.json, lifecycle-tier.log, runner/ (slot.sh, meter.py, run_case.sh without the machine's network proxy settings), MANIFEST.sha256 (sha256 of every other file).
