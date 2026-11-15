# Generated loop obligations: Counter.bump

This directory turns one loop's exported edges and a candidate invariant into the exact
obligations of initiation, preservation (every back edge), termination, exit and outcome, and
discharges them with the existing runner, [`Verify/Discharge/discharge.sh`](../../Discharge/discharge.sh).
Unlike [`../chc`](../chc) (Horn clauses written by hand), nothing here is written by hand except the
mutated candidate of the negative test: the edges come from solar-verify's encoding of the function,
the obligations from the generator, the proofs from the discharge backends.

The loop is `Counter.bump` of [`Certified/verify_counter/verify_counter.sol`](../../../Certified/verify_counter/verify_counter.sol):
`for (uint256 i = 0; i < n; i++) count++;` after `require(count + n <= limit)`, annotated with
`i <= n`, `count == old(count) + i` and `decreases n - i`.

## Input: the loop's edges

`stub/` is a **stub** of the loop export, in place until solar's frozen loop exporter (branch
`alpharush/loopvc-export`, `docs/loopvc-interface.md`) lands; the generator reads only the fields
listed below, so moving to that interface changes `loopvc_main`'s reader, not the obligations.
It was written by solar-verify at solar `902cccc2` with [`stub/solar-stub.diff`](stub/solar-stub.diff)
applied, from this repository's root:

    SOLAR_VERIFY_LOOPVC_STUB=Verify/Infer/loopvc/stub solar-verify --no-infer --only Counter.bump \
      Certified/verify_counter/verify_counter.sol

Two runs write identical bytes. The diff reuses solar-verify's Horn encoding of loops
(`crates/verify/src/vc/horn.rs`: each clause is the function's real-run definitions, sliced to the
clause's cone, universally closed) and changes four things:

- it writes the encoding for every loop of the run, not only after an obligation failed;
- the cutpoint's parameters include the pre-state values (`old.count`, `old.limit`, ...). Without
  them horn.rs's encoding cannot state `count == old(count) + i`, and Spacer answers `unsat` (no
  invariant) for this loop;
- the edges also include each reverting path of the body (the checked `count++` and `i++`) and every
  obligation after the loop (the postcondition and the contract invariant);
- the annotated invariants are not assumed at the head, so each edge is the loop's transition, not
  one conditioned on the candidate.

Files:

- `Counter.bump.loop0.horn.smt2`: the Horn view, one predicate `Inv` per cutpoint, one clause per
  edge (`forall xs. (=> (and facts... (Inv args)) head)`).
- `Counter.bump.loop0.json`: what the generator reads: `unit`, `loop`, `horn`; `cutpoints[]`
  (`predicate`, `id`, `params[].name`, `span`); `edges[]` in clause order (`id`, `kind`: `entry`,
  `back`, `call`, `exit`, `revert` or `oog`; `outcome`; `span`; `check`; `supported`);
  `candidates[]` (`id`, `origin`, `cutpoint`, `clauses[]` with `text`, `smt` over the parameters
  as `|name|`, `span`); `rankings[]` (`cutpoint`, `smt`, `text`, `span`).
- `Counter.bump.loop0.spacer.out`: z3 4.13.4's Spacer answer for the Horn view, unedited.

## Obligations

`smt2lean_inv.py loopvc` reads each clause `forall xs. facts ∧ P1(a1) ∧ ... → H` and writes, per
obligation, a script that declares `xs` and asserts `facts` in order, a guard, and a goal:

| Head `H` | Obligations (manifest `kind`) |
| --- | --- |
| `Q(b)` on an entry, back or call edge | one per clause `φ` of Q's candidate: `φ(b)` (`initiation`, `preservation`, `call`) |
| `P(b)` on a back edge of `P` with a ranking `r` | `0 <= r(a) ∧ r(b) < r(a)` (`termination`) |
| a formula on an exit edge | the formula (`exit`): postcondition, contract invariant |
| a formula on a revert edge | the reverting condition is false at the site (`outcome-revert`) |

The guard is every clause of every body cutpoint's candidate at its arguments, so each goal is
proved assuming the whole invariant (joint induction of mutually supporting clauses), and each
cutpoint has its own candidate. A candidate is applied by substitution, SMT-LIB's meaning of a
`define-fun` application, and terms are written in `Verify/Obligation`'s embedding exactly as solar's
`crates/verify/src/lean.rs` writes them, so `obK.Valid` holds exactly when the query in
`LoopVc/<C>/<f>_loop<N>.obK.smt2` is unsat. The export is a `solar-verify-lean` version-2 export
(`manifest.json` with the sources and their hashes, one module), so `discharge.sh` applies its own
checks unchanged: semantics hashes, required manifest, locked inputs, per-row axioms, vacuity.

Normal exits, reverts and out-of-gas stay separate edges and separate rows. Nothing is proved by a
solver's answer: `vc_smt` rebuilds cvc5's proof in the kernel and every row's axioms are checked.
An edge the exporter could not write, a candidate clause that names anything but the cutpoint's
parameters, or a construct outside the embedding becomes a required unit with no module, which
`discharge.sh` fails as not exported: inconclusive, never proved. Unknown, timeout and errors fail
their row.

`smt2lean_inv.py cti DIR`, after a discharge, asks z3 for a model of each open obligation's query
and writes `discharge/cti.json` (candidate, edge, kind, source location, the cutpoint state before
and after the edge) and `discharge/residual/<id>.lean`, the exact goal left open. A model is a
counterexample to induction: it rejects the candidate on that edge, and says nothing about whether
the state is reachable.

## Results

`check.sh` is the acceptance check; [`results/`](results) holds its run (z3 4.13.4, cvc5 through lean-smt
`6b26285`, Lean 4.35.0):

| Candidate | Obligations | Proved | Vacuous | Axioms |
| --- | --- | --- | --- | --- |
| annotated (`i <= n`, `count == old(count) + i`, `decreases n - i`) | 9 | 9 (`vc_smt`) | none | propext, Classical.choice, Quot.sound |
| Spacer's, with the annotated ranking | 11 | 11 (`vc_smt`) | none | propext, Classical.choice, Quot.sound |
| mutant (`count == old(count) + i + 1`) | 9 | 5 | none | rejected: 4 rows with a counterexample |

The mutant's counterexamples: on the entry edge, `count = old.count = i = n = 0` after the edge
(the mutant needs `count = 1`); on the first revert edge, the exit edge's postcondition and the
contract invariant. `vc_valid` proves none of the rows within its 30 s; `vc_smt` proves them all.

    Verify/Infer/loopvc/check.sh [WORKDIR]

needs the library build of `Verify/Discharge/Reconstruct` (see `Verify/Discharge/README.md`) and z3
on `PATH`. It regenerates both exports and compares them byte for byte with `export/`, discharges
each against its lock (`export/<candidate>.sha256`, the `inputs.sha256` format of `DISCHARGE_LOCK`),
requires every row proved, non-vacuous and with the three axioms, then requires the mutant to fail
with a counterexample on the entry edge. Regenerate `export/` with
`smt2lean_inv.py loopvc --interface stub/Counter.bump.loop0.json --root . --out ...` from the
repository root (`--spacer stub/Counter.bump.loop0.spacer.out` for Spacer's candidate).

## Not covered

- The input is the stub above, not the frozen exporter, and nothing here proves that the exported
  edge formulas are, or are implied by, the transition relation of SolidCore's semantics of
  `bump`; that bridge belongs to the exporter.
- The obligations are not composed by `Verify/VC/EndToEnd`: they are not part of a script that
  `checkScript` binds to the function's erased tree (`Binds`), so no bytecode theorem uses them yet.
- Out of gas: solar-verify has no gas model, so the export has no `oog` edge.
- Cutpoint parameters are Int and Bool only (horn.rs's fragment): no storage arrays, mappings or
  memory. A loop that needs them gets an unsupported edge.
- Only reverts inside the loop are loop edges; the `require` and the checked `count + n` before it
  are not.
- No bounded replay of a counterexample, and no strengthening from it.
