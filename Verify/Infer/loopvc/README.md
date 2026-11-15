# Generated loop obligations: Counter.bump

This directory turns solar-verify's loop-cut interface for one loop and a candidate invariant into
the exact obligations of initiation, preservation (every back edge), termination and exit, and
discharges them with the existing runner, [`Verify/Discharge/discharge.sh`](../../Discharge/discharge.sh).
Unlike [`../chc`](../chc) (Horn clauses written by hand), nothing here is written by hand except
the mutated candidate of the negative test.

The loop is `Counter.bump` of [`Certified/verify_counter/verify_counter.sol`](../../../Certified/verify_counter/verify_counter.sol):
`for (uint256 i = 0; i < n; i++) count++;` after `require(count + n <= limit)`, annotated with
`i <= n`, `count == old(count) + i` and `decreases n - i`.

## Input

- `solar/`: the loop-cut interface solar-verify writes (`--emit-loopvc`, format 1, solar's
  `docs/loopvc-interface.md`), at the solar commit in `solar/REV`, run from this repository's root:

      solar-verify --no-infer --only Counter.bump --emit-loopvc DIR Certified/verify_counter/verify_counter.sol

  `Counter/bump.loopvc.json` (cut, parameters, edges, templates, revert paths, the run's
  candidate), `Counter/bump.horn.smt2` (the Horn view), `Counter/bump.script0.smt2` (the run's
  script), `Counter/bump.lean` (the run's obligations, `--emit-lean`), `Counter/bump_loopvc.lean`
  (the templates, with the run's candidate abstracted, and `tK_exact`: their instances at the run's
  candidate are the run's obligations, by `rfl`) and `LoopVc.lean` (`Template.instances`).
- `spacer/Counter.bump.spacer.out`: z3 4.13.4's Spacer answer for the Horn view, unedited.
- `candidates/Counter.bump.mutant.json`: the annotated candidate with `count == old(count) + i`
  changed to `+ i + 1`.

## Obligations

`smt2lean_inv.py loopvc --export solar --unit Counter.bump [--candidate F | --spacer F]` writes the
candidate's obligations as a `solar-verify-lean` version-2 export (`export/<candidate>/`):

- The candidate (the interface's own, a candidate file in its shape, or Spacer's model of the cut
  predicate with the interface's ranking function) is translated into the embedding, numbered as
  the run's script declares its symbols; a term naming anything but the cut's parameters is refused.
- Lean computes the obligations: `Template.instances` of every template at the candidate, printed as
  terms, one `obK` per instance. Nothing re-implements the instantiation.
- `bridge/.../*_bridge.lean` proves, by `rfl`, that each template's instances at the candidate are
  exactly those `obK` (and, for the annotated candidate, that it is the run's candidate, so its
  obligations are the run's own through the interface's `tK_exact`). The generator checks it and
  its axioms before it writes the manifest.

| Template | Edge | Obligations (manifest `kind`) |
| --- | --- | --- |
| `invariant` | entry | one per conjunct (`initiation`) |
| `invariant` | back | one per conjunct, each assuming the whole invariant at the head (`preservation`) |
| `rank` | back | `0 <= r` and `r` decreases, under the invariant (`termination`) |
| `path` | exit | postcondition, contract invariant (`exit`) |

Revert paths owe nothing without `succeeds-if` (the interface's contract): the manifest lists them,
with their conditions, and they have no row. Out of gas is not in solar-verify's encoding.

`discharge.sh` applies its own checks unchanged: semantics hashes, required manifest, locked
inputs, per-row axioms, vacuity. Nothing is proved by a solver's answer: `vc_smt` rebuilds cvc5's
proof in the kernel. A failed, unknown or timed-out row is not proved.

`smt2lean_inv.py cti DIR`, after a discharge, asks z3 for a model of each open obligation's query
(the template's SMT-LIB with the candidate put back, `LoopVc/.../*.obK.smt2`) and writes
`discharge/cti.json` (candidate, template, edge, source location, the cut's parameters before and
after the edge) and `discharge/residual/<id>.lean`, the exact goal left open. A model is a
counterexample to induction: it rejects the candidate on that edge, and says nothing about whether
the state is reachable.

## Results

`check.sh` is the acceptance check; [`results/`](results) holds its run (z3 4.13.4, cvc5 through
lean-smt `6b26285`, Lean 4.35.0):

| Candidate | Obligations | Proved | Vacuous | Axioms |
| --- | --- | --- | --- | --- |
| annotated (`i <= n`, `count == old(count) + i`, `decreases n - i`) | 7 | 7 (`vc_smt`) | none | propext, Classical.choice, Quot.sound |
| Spacer's, with the annotated ranking function | 9 | 9 (`vc_smt`) | none | propext, Classical.choice, Quot.sound |
| mutant (`count == old(count) + i + 1`) | 7 | 4 | none | rejected: 3 rows with a counterexample |

The mutant's counterexamples: on the entry edge (`t0`), `count = i = n = old(count) = 0` after
it, where the mutant needs `count = 1`; on the exit edge, the postcondition (`t3`) and the
contract invariant (`t4`) from the head state `count = 1, i = n = old(count) = 0`.

    bash Verify/Infer/loopvc/check.sh [WORKDIR]

needs the library build of `Verify/Discharge/Reconstruct` (`Verify/Discharge/README.md`) and z3 on
`PATH`. With `SOLAR_VERIFY` set to a solar-verify built at `solar/REV`, it first checks that
solar-verify writes the committed interface files. It then regenerates both exports and compares
them byte for byte with `export/` (the bridge checks in that step), discharges each against its lock
(`export/<candidate>.sha256`), requires every row proved, non-vacuous and with the three axioms, and
requires the mutant to fail with a counterexample on the entry edge. CI runs it (`.github/workflows/loopvc.yml`).

## Not covered

- Not composed by `Verify/VC/EndToEnd`: the obligations are not yet part of a script that
  `checkScript` binds to the function's erased tree (`Binds`), so no bytecode theorem uses them.
- Out of gas: solar-verify has no gas model. Revert paths carry no obligation (no `succeeds-if`).
- The interface's limits (format 1): one loop per function, no call in the loop, Int and Bool cut
  parameters, inference off.
- CI does not rebuild solar to recheck the interface files (`SOLAR_VERIFY` unset there); the
  committed files' hashes are pinned in the locks.
- No bounded replay of a counterexample, and no strengthening from it. `vc_valid` proves none of the
  rows within its 30 s; `vc_smt` proves them all.
