# Discharging solar-verify's VCs in the kernel

`solar-verify --emit-lean DIR FILE.sol` (solar, `crates/verify`) writes each query it sends a
solver as a Lean term `ob : Obligation` whose `ob.Valid` (Verify/Obligation/Vc.lean) holds exactly
when the query is unsatisfiable. This directory decides which of them are proved. A VC is
accepted only when a certificate the Lean kernel checks proves `ob.Valid` and the proof uses no
axiom but `propext`, `Classical.choice` and `Quot.sound`; a solver's answer alone never counts.

## Backends

| Backend | What proves `ob.Valid` | Where |
| --- | --- | --- |
| `vc_smt` | cvc5 refutes the goal (in-process, through lean-cvc5's plugin) and lean-smt rebuilds its proof step by step as a Lean term; a step it cannot rebuild is a `sorryAx` and fails the row's axiom check | Reconstruct/ (a package of its own, so building this repository fetches no solver) |
| `vc_valid` | unfolds the obligation to a shallow goal and searches for a proof (case splits, congruence, `omega`, and `vc_ground`, which decides closed hypotheses by kernel evaluation) | Search.lean, Valid.lean, Leaf.lean, Sat/Ground.lean |
| `cert` | a theorem written for the obligation (such as one under Contracts/<Contract>/), named in a certificate list; its proof may check an LRAT certificate with `Sat` | DISCHARGE_CERTS |

`Sat` (Cnf, Lrat, Load) checks LRAT refutations of CNF formulas in the kernel (`check_sound`);
test/sat/Sat.lean checks one. It reaches a VC only through a `cert` certificate: turning an
obligation into CNF needs a bit-blaster with a soundness proof, which is parked until a VC needs it.

## Running

```text
(cd Verify/Discharge/Reconstruct && lake build -KleanMemory=3000)
DISCHARGE_LOCK=Verify/Discharge/frozen/v2/<C>.sha256 DISCHARGE_SOURCE_ROOT=<solar at 7f4e94e> \
  Verify/Discharge/discharge.sh DIR [TIMEOUT_SECONDS]
```

One runner, one library build (Reconstruct/, which compiles Verify/Obligation and
Verify/Discharge from this repository's sources), backends tried in the order
DISCHARGE_BACKENDS gives, default `smt=vc_smt;vc_valid=vc_valid`30`: cvc5 reconstruction first,
`vc_valid` as the fallback with 30 s. The script states every obligation itself
(`theorem obligation : <ob>.Valid := ...`), so every backend is checked against the exported
statement, and applies the same checks to all: the manifest format and version, the hashes of
Smt.lean and Vc.lean the export was written for, no unchecked construct in Verify/Obligation,
every required obligation present once, the inputs against DISCHARGE_LOCK, and per row the exit
status, errors, a timeout and the axioms `Lean.collectAxioms` reports. Backend sources are never
grepped: lean-smt's contain `sorry`, and only what a row's proof actually uses counts.

It writes DIR/discharge/results.tsv (one row per obligation and backend tried) and summary.tsv
(per obligation, the backends that proved it, and `vacuous`), and exits 0 only when every
required obligation is proved. The `vacuous` column (DISCHARGE_VACUITY, on by default) tries
`{ ob with goal := .bool false }` with `vc_smt`: `yes` when the kernel proves it with clean axioms,
so the row's hypotheses are contradictory and it holds vacuously (the path it covers is
unreachable); `no` when cvc5 finds a model of the hypotheses; `unknown` otherwise. It never
changes a verdict. DISCHARGE_ALL=1 tries every backend on every obligation to measure coverage.
The header of discharge.sh lists the other settings.

Version-1 exports (and the version-2 locks derived from them) say `import SolarVerify` and record the hash of
Vc.lean with its old first line; the script compiles them with `import Verify.Obligation` and
accepts either hash, nothing else.

## Frozen inputs and negatives

frozen/<C>.sha256 and frozen/PINS are solar's version-1 locks of the Counter, Token, Vault and
ArrayMax exports, kept as they were. frozen/v2/ holds the version-2 locks, provisional (frozen/v2/PINS says
how they were made). test/negatives.sh corrupts one input at a time (an edited source, an edited
module, a deleted required obligation without a lock, a duplicated obligation, an absolute source
path, version 1) and requires each run to fail with its message before any Lean runs.
test/smt-negatives.sh edits one obligation at a time so that it no longer holds (Counter
increment's goal and the assertion defining the new count read as `+ 2`, Vault withdraw#0's
and ArrayMax max#8's goals negated) and requires every backend to fail on it by a counterexample
or an incomplete answer, never a timeout, while the same untouched rows are proved.

## Results on the frozen version-2 locks

results/v2/ holds the run of the default backends on the four locked exports
(results/v2/README.md).
