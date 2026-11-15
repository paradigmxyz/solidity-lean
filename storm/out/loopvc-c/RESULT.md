# loopvc-c: loop obligations as required registry entries in the certify driver

**Status (interim, 2026-11-15 03:10 UTC):** the driver's tests pass (`tools/certify/test.sh`: 97 ok,
0 failed) and removing one loop obligation from verify_counter's export stops `scripts/certify` at step 3b.
The full cold run of `scripts/certify` on verify_counter at this bundle and solidity-lean d6e066f5 is
still running; `verify_counter.log` will hold it. Nothing here claims verify_counter is CERTIFIED.
Nothing has been pushed to paradigmxyz/solar or to alpharush/certified-translation.

## What is delivered

- `loopvc-c.bundle`: one commit, 78a5ef880282649d4feafffd539e352980d949d8, on top of solar
  `alpharush/certified` 902cccc2 (PR #2637). `git bundle verify` passes against 902cccc2.
  The same commit as `0001-feat-certify-require-and-discharge-the-loop-obligati.patch`.
- solidity-lean `alpharush/loopvc-driver` d6e066f5 (on 6dd035dc): `Certified/verify_counter/loopvc.json`
  (the registry) and a paragraph in `Certified/README.md`. The bundle pins solidity-lean.rev to d6e066f5.

## What the commit does

1. **solar-verify --emit-lean names the cutpoint edge of every loop obligation.** Each obligation past a
   loop head carries `cut` = {`loop` (L<line>:<col>), `edge` (entry, back, exit), `class` (initiation,
   preservation, termination, body, call, exit), `merged`} and an `outcome` (normal or revert); each unit
   lists its `cutpoints` with their invariants, decreases clauses, inferred invariants and measure, back
   edges and exits. The Lean modules are unchanged (snapshots pass). New test `emit_lean_cutpoints`.
2. **`tools/certify/loopvc.py`** derives a function's registry from that export and checks a committed one:
   - derive requires, per cutpoint and from its own clauses, one initiation per invariant (entry edge), one
     preservation per invariant and one termination per ranking (back edge), at least one normal-outcome
     obligation on the exit edge; it refuses a loop with no ranking, a break or continue (one obligation
     would cover several edges) and a return in the body that joins the exit path.
   - check: the export must be exactly the registry (ids, edges, classes, outcomes, each query's
     smt_sha256, the exported module's sha256, the Lean semantics hashes, the source hash) for this run's
     bytecode and the committed record's; with the discharge's summary, every registry obligation must be
     proved, its proof's axioms within propext, Classical.choice and Quot.sound, not vacuous, and on this
     export's inputs. Failed, timeout, skipped, missing, another axiom: inconclusive, the run fails.
3. **`scripts/certify`**: step 3b exports the source with `solar-verify --dry-run --emit-lean` and runs the
   check before any Lean; step 6 builds `Verify/Discharge/Reconstruct` from the pinned checkout and runs
   `Verify/Discharge/discharge.sh` on the export inside `sandbox.sh` (writing only the export directory),
   then the check with the summary. The record gets `statuses.loops` and `loops` (the receipt).
4. **`tools/certify/test.sh`** builds solar-verify when SOLAR_VERIFY is unset, so the cases run in CI's
   certify job: 21 loop cases (registry ok; dropped preservation, exit and termination; not required;
   changed query; changed module; registry lacking one; other bytecode; record's other bytecode; no
   ranking; break; return in body; discharged ok; timeout; missing row; sorryAx; vacuous; other export;
   the driver binding at 3b; the driver failing on an export without one loop obligation).

## verify_counter (Counter.bump)

Registry `Certified/verify_counter/loopvc.json` (sha256 82cfe545...), one cutpoint L26:9:

| id | edge | class | clause |
| --- | --- | --- | --- |
| Counter.bump#0 | entry | initiation | i <= n |
| Counter.bump#1 | entry | initiation | count == old(count) + i |
| Counter.bump#39 | back | preservation | i <= n |
| Counter.bump#40 | back | preservation | count == old(count) + i |
| Counter.bump#41 | back | termination | n - i (0 <= d0 and d1 < d0) |
| Counter.bump#43 | exit | exit | ensures count == old(count) + n |
| Counter.bump#44 | exit | exit | invariant count <= limit |

Outcomes: all seven normal; revert none (require over and Panic(0x11) change nothing); out of gas none.
`discharge/`: discharge.sh on that export (smt = lean-smt reconstruction of cvc5; 14 of 14 of the contract
proved, each loop row axioms propext Classical.choice Quot.sound, vacuity no), and `loopvc-receipt.json`,
the check of the committed registry against it.

## Acceptance checks run

- `tools/certify/test.sh` at 78a5ef88 (`test.log`): exit 0, 97 ok, 0 FAIL; skips: foreign-solar (built from
  this checkout) and the older spec cases (SOLAR_VERIFY unset, as in CI).
- `negative-drop-preservation.log`: `scripts/certify` on Certified/verify_counter at d6e066f5 with a
  solar-verify that drops Counter.bump#39 from its export: `loopvc: Counter.bump cutpoint L26:9: invariant
  i <= n has 0 preservation obligations on the back edge, not one`, exit 1, no CHECKED line.
- `cargo test -p solar-verify` (all pass), `cargo clippy -p solar-verify --all-targets` (clean).

## Not covered

- The obligations are solar-verify's SMT encoding of the loop, exported mechanically and discharged in
  the kernel; they are not yet derived from SolidCore's denotation through WP (lane A), and the registry
  does not by itself compose them into the published statement (Verify/VC/EndToEnd is not invoked on them).
- Call edges: bump has none; a callee's precondition met in a loop is classed `call` but has no test.
- Loops with break/continue/return-in-body are refused by derive, not split per edge.
- Solar's own CI has not run this commit (it is a bundle, not a pushed branch).
