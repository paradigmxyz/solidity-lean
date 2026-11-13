# Discharging solar-verify's VCs in the kernel

`solar-verify --emit-lean DIR FILE.sol` (solar, `crates/verify`) writes each query it sends a
solver as a Lean term `ob : Obligation` whose `ob.Valid` (Verify/Obligation/Vc.lean) holds exactly
when the query is unsatisfiable. This directory decides which of them are proved. A VC is
accepted only when a certificate the Lean kernel checks proves `ob.Valid` and the proof uses no
axiom but `propext`, `Classical.choice` and `Quot.sound`; a solver's answer alone never counts.

## Certificate kinds

| Kind | What proves `ob.Valid` | Where |
| --- | --- | --- |
| `search` | `vc_valid`: unfolds the obligation to a shallow goal and searches for a proof (case splits, congruence, `omega`, and `vc_ground`, which decides closed hypotheses by kernel evaluation) | Search.lean, Valid.lean, Leaf.lean, Sat/Ground.lean |
| `smt` | `vc_smt`: cvc5 refutes the goal and lean-smt rebuilds its proof step by step as a Lean term; a step it cannot rebuild is a `sorryAx` and fails the axiom check | ../Reconstruct (a package of its own, so building this repository fetches no solver) |
| `lean` | a theorem written for the obligation (such as one under Contracts/<Contract>/), named in a certificate list; its proof may check an LRAT certificate with `Sat` | DISCHARGE_CERTS |

`Sat` (Cnf, Lrat, Load) checks LRAT refutations of CNF formulas in the kernel (`check_sound`);
test/sat/Sat.lean checks one. It reaches a VC only through a `lean` certificate: turning an
obligation into CNF needs a bit-blaster with a soundness proof, which is parked until a VC needs it.

## Running

```text
lake build VerifyDischarge
DISCHARGE_KINDS=search,smt Verify/Discharge/discharge.sh DIR [TIMEOUT_SECONDS]
```

The script states every obligation itself (`theorem obligation : <ob>.Valid := ...`), so every
kind is checked against the exported statement, and applies the same checks to all: the manifest
format and version, the hashes of Smt.lean and Vc.lean the export was written for, no unchecked
construct in the libraries, every required obligation present once, the inputs against
DISCHARGE_LOCK, and per proof the exit status, errors, a timeout and the axioms. It writes
DIR/discharge/results.tsv (one row per obligation and kind) and summary.tsv (per obligation, the
kinds that proved it), and exits 0 only when every required obligation is proved. DISCHARGE_ALL=1
tries every kind on every obligation to measure each kind's coverage. The header of discharge.sh
lists the other settings.

Version-1 exports (and the version-2 locks derived from them) say `import SolarVerify` and record the hash of
Vc.lean with its old first line; the script compiles them with `import Verify.Obligation` and
accepts either hash, nothing else.

## Frozen inputs and negatives

frozen/<C>.sha256 and frozen/PINS are solar's version-1 locks of the Counter, Token, Vault and
ArrayMax exports, kept as they were. frozen/v2/ holds the version-2 locks (frozen/v2/PINS says
how they were made). test/negatives.sh corrupts one input at a time (an edited source, an edited
module, a deleted required obligation without a lock, a duplicated obligation, an absolute source
path, version 1) and requires each run to fail with its message before any Lean runs.
