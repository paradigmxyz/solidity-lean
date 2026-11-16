# Held-out H1 (SimpleStorage): REJECTED, exit 1

- Case: tests/heldout/rc-2026-11-15/SimpleStorage/SimpleStorage.sol --contract SimpleStorage, held-out set e0564a28 (source sha256 928cc1594907cb4d56183be7565db8b60bee77c2ffc9fc731083bf31dc1bc082)
- Driver: solar 800d78a98b9e64612c742d5038e7e2ec35dd52b4 (tree eff1b722c1ab2ee4a0574ff830147eca06ead23f, clean checkout), solidity-lean base 44572c150176365fa5e0d56ae6c59a7a443f8122, solc 0.8.35, Lean v4.35.0
- Command: see record.json "command" (natspec spec, default requested tier certified, --packages-from/--probe-cache a prebuilt solidity-lean 44572c15 package cache)
- Verdict: REJECTED, exit 1. requested_tier certified; no tier reached (the record carries no statuses: scripts/certify --require-final exited 1 in its spec stage)
- Reason (driver): "spec: get_meets0 does not check: omega could not prove the goal: (SpecConnect.lean:163)". spec_connect refuses the functions of SimpleStorage; get_holds and get_holds_in depend on sorryAx.
- Reason (full Lean message, a diagnostic re-elaboration of the same generated SpecConnect.lean in the run's work tree, not part of the driver run):
  SpecConnect.lean:163:5: omega could not prove the goal; a possible counterexample may satisfy a <= 1 where a := pre.time
- set(uint256): its spec_connect theorems checked (set_holds, set_holds_in: propext, Classical.choice, Quot.sound only). get(): not proved.
- The spec is unchanged from the held-out set (get: succeeds-if msg.value == 0, ensures result == num). The failing theorem is the generated proof of get's ensures against its erased tree (a 32-byte return of slot 0), so this rejection is in the generic stage's spec proof for a returned value.
- Probe: typecheck ok; constructor returns; storage []; get(), num(), set(uint256) agree.
- Envelope: source inside (functions get(), num(), set(uint256)); bytecode has no call, creation, gas or return-data opcode; gas bound 1944803
- bytecode_sha256 6e95f821ecc2c71682bb59cd089429e0ab967f2cb33da8a32ffbce7135e9d402
- Wall 3649.7 s (driver started 00:25:20Z, finished 01:26:08Z on 2026-11-16 UTC); peak RSS: largest process 5279 MB, process tree 6181 MB (slot-receipt.json), LEAN_NUM_THREADS=1, LEAN_MEMORY 6000
- Lifecycle tier: '--tier lifecycle' on the same driver is a usage error (tier not offered: choices compiled, functional, certified), exit 2 (lifecycle-tier.log). It is not a BLOCKED exit.
- No replay: there is no certified record to replay. No tampered-claim replay for the same reason.
- An earlier H1 run on driver 1844041e was stopped after 19 minutes, before it wrote a record, to move it to this pin; it has no verdict.
- runner/: the scripts that ran it (slot.sh, meter.py, run_case.sh; run_case.sh as published omits the Hand's network proxy settings).

Files: driver.log (driver stdout and stderr), certify.log, record.json, inputs/ (archived inputs), SimpleStorage.sol, slot-receipt.json, lifecycle-tier.log, MANIFEST.sha256 (sha256 of every other file here).
