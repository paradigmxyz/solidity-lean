# Default backends on the frozen version-2 locks

Kernel-checked proofs of the 63 required obligations of the four example exports, by
`Verify/Discharge/discharge.sh` with its defaults (`DISCHARGE_BACKENDS='smt=vc_smt;vc_valid=vc_valid@30'`,
vacuity on), 120 s per attempt, `LEAN_NUM_THREADS=1`. Formula-level evidence only: each row
proves `<ob>.Valid` over Verify/Obligation; nothing here relates the SMT encoding to source or
bytecode semantics.

Inputs: the exports frozen/v2/<C>.sha256 pins (provisional, see frozen/v2/PINS), each run with
`DISCHARGE_LOCK=frozen/v2/<C>.sha256` and `DISCHARGE_SOURCE_ROOT` a paradigmxyz/solar checkout at
7f4e94e; each `<C>/inputs.sha256` equals its lock. Backend: Verify/Discharge/Reconstruct (Lean
v4.35.0, lean-smt 6b26285, lean-cvc5 d19a134 with its bundled cvc5, in-process via `--plugin`).

| Contract | Proved | By smt | By vc_valid | Vacuous |
|---|---|---|---|---|
| Counter | 14/14 | 14 | 0 | 0 |
| Token | 13/13 | 13 | 0 | 0 |
| Vault | 17/17 | 17 | 0 | 5 |
| ArrayMax | 19/19 | 19 | 0 | 0 |
| Total | 63/63 | 63 | 0 | 5 |

Every proof's axioms are exactly `propext Classical.choice Quot.sound` (`<C>/results.tsv`,
column axioms). smt took at most 6.4 s and 1,885 MB per obligation, 219 s for all 63; the
vc_valid fallback was never needed.

Vacuous (`<C>/summary.tsv`, column vacuous): the kernel also proves `{ ob with goal := .bool false }`
for Vault.deposit#6, deposit#7, withdraw#6, withdraw#7 and withdraw#8, all in the script that
re-enters while `locked`: their hypotheses are contradictory, so they hold only because that path
is unreachable. Of the other 58, cvc5 finds a model of the hypotheses for 27 (`no`) and gives up
on 31 (`unknown`, quantified hypotheses).

Negatives: test/negatives.sh, 11/11 on each of the four exports (input mismatches, including a
missing certificate export and a stale same-name module on the certificate path, all failing
before any Lean runs). test/smt-negatives.sh, run with both default backends (`smt-negatives.tsv`): every
edited obligation fails under smt by a cvc5 model (N2, N3; "either it is false") or an
incomplete answer (N4), in at most 3.7 s, never a timeout, while the same untouched rows are
proved. vc_valid fails N2, N3 and N4 on Vault by an omega counterexample, but the negated ArrayMax
max#8 only by its 30 s timeout, so the script now checks the smt backend alone by default.
