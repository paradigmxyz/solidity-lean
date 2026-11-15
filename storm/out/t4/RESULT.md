# Loop certificates through the certify driver (T4)

- solidity-lean: branch alpharush/loopvc-t4, head 0fbc835d, base bc6da61b. Adds Verify/Infer/loopvc/
  (loopcert.py, run.sh, Bridge.lean, README.md, tests/test.sh, tests/heldout/Drain.sol and
  Drain.invariants.json). Nothing else changes.
- solar scripts/certify: scripts-certify-loopcert.patch, against 902cccc2 (steps 3b and 6 call
  Verify/Infer/loopvc; --invariants FILE; a blocked or unproved loop fails the run). It replaces the
  registry steps of 68903b85 and keeps its find_verify and spec_export_fresh helpers.
- solar-verify: solar-verify-loopvc-literal-params.patch, against 1c38646b (crates/verify/src/vc/infer.rs):
  a literal value (a named return's 0 at entry, a constant local) is no cut parameter. Without it a
  loop whose function has a named return is blocked with "0 undeclared".

## Receipts

Checker tests (Verify/Infer/loopvc/tests/test.sh, solar-verify 1c38646b plus the patch, solc 0.8.35):
10 of 10 ok (test.log).

| case | expected | got |
|---|---|---|
| Counter.bump (for loop, annotations) | proved | proved, 14 of 14 discharged |
| Drain.drain (held-out while loop, supplied invariants) | proved | proved, 7 of 7 discharged |
| annotated copy's runtime bytecode | equal | equal |
| invariant not preserved | failed | failed |
| no decreases | blocked | blocked |
| call in the loop | blocked | blocked |
| two loops | blocked | blocked |
| candidate edited in the template module | failed | failed (kernel rejects tK_exact) |
| Horn view edited | blocked | blocked |

Driver (driver-verify_counter.log): solar 902cccc2 plus the scripts/certify patch, solidity-lean
d6e066f5 plus Verify/Infer/loopvc from 0fbc835d (Verify/Discharge and Verify/Obligation identical
to bc6da61b), --no-negatives, CERTIFY_REPLAY_TRUST_UPSTREAM=1, warm build. Exit 0, CHECKED
verify_counter, loops: proved in the kernel: Counter.bump (5 templates, theorem
LoopCert.Counter.bump.certified). Receipt: receipt-verify_counter.json.

Driver negatives: no decreases on bump fails at 3b with exit 1, before any Lean
(driver-neg-nodecreases.log). Invariants supplied with --invariants to a source without loop
annotations: inserted, runtime bytecode unchanged, Counter.bump required
(driver-supplied-invariants.log, stopped at step 5).

## Not covered

- Bridge.lean states ForBinds/WhileBinds and proves forLoop_of_cut/whileLoop_of_cut onto SolidCore's
  loop rule; the per-function binding is not generated, so a loop certificate is a checked fact about
  solar-verify's encoding, not yet a source-to-bytecode theorem by itself.
- Calls inside loops, several loops per function, more than one decreases: blocked. Internal calls
  outside loops are only covered as solar-verify encodes them.
