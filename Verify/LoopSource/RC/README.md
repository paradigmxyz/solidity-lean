# Loop obligations from solar-verify, bound to the source loop bridge

Two loops, each checked from the obligations solar-verify itself emitted (`--emit-lean`), not
from handwritten models:

- `inputs/Counter.sol`, `Counter.bump`: a `for` loop over a storage counter (the existing
  certification target).
- `inputs/Gcd.sol`, `Gcd.gcd`: chosen as the held-out case because it is not Counter-shaped: a
  `while` loop with a `!=` guard, a branching body that writes one of two locals, a sum as its
  measure, and no storage.

## Reproduce

solar-verify from solar `c09510a39b5c9940845d2c19928c742f676b8675` (`cargo build -p solar-verify`;
the crates are the same at `800d78a98b9e64612c742d5038e7e2ec35dd52b4`), z3 5.4.1 as
`SOLAR_VERIFY_Z3`:

```
solar-verify --no-infer --only Counter.bump --emit-lean emit/counter inputs/Counter.sol
solar-verify --no-infer --only Counter.bump --dump-lean RC/Counter/Script.lean \
  --lean-namespace Verify.LoopSource.RC.Counter inputs/Counter.sol
python3 Verify/LoopSource/gen_loopvc.py emit/counter/manifest.json \
  Verify.LoopSource.RC.Counter.Script Verify.LoopSource.RC.Counter RC/Counter/Obligations.lean
python3 Verify/LoopSource/matrix.py counter=emit/counter/manifest.json ...
python3 Verify/LoopSource/witness.py emit/counter/manifest.json 'Counter.bump#5' z3 \
  --assume '(>= |n@21| 3)' --assume '(>= |count@17| 5)' n@21 count@17 limit@18
```

and the same for `Gcd.gcd` (probe `Gcd.gcd#3`, `--assume '(= |a@19| 12)' --assume '(= |b@20| 18)'`).
The emitted modules are kept as `emit/*/*.lean.txt` so the library build does not take them.

## Acceptance gate

`Verify/LoopSource/loopgate.py` runs solar-verify on one function and decides each outcome apart
(`gate/<case>/gate.json`, `gate/<case>.txt`): initiation, consecution, termination, exit (every
obligation of that kind unsat; a missing loop kind rejects with exit 3) and **nonvacuity, required**:
the advisory probe sat and a z3 model of it (`witness.py`) with the given `--assume` facts. Exit 0
ACCEPT, 1 an obligation failed, 2 solar-verify error, 3 a loop kind missing, 4 VACUOUS.

| case | gate exit | init | consec | term | exit | nonvacuity |
|---|---|---|---|---|---|---|
| Counter | 0 ACCEPT | 0 | 0 | 0 | 0 | 0 (n=3, count=5, limit=8) |
| CounterBadInit | 1 | 1 | 0 | 0 | 0 | 0 |
| CounterBadPres | 1 | 0 | 1 | 0 | 0 | 4 |
| CounterBadDecr | 1 | 0 | 0 | 1 | 0 | 0 |
| CounterBadExit | 1 | 0 | 0 | 0 | 1 | 0 |
| Gcd | 0 ACCEPT | 0 | 0 | 0 | 0 | 0 (a=12, b=18) |
| GcdBadInit | 1 | 1 | 0 | 0 | 0 | 0 |
| GcdBadPres | 1 | 0 | 1 | 0 | 0 | 0 |
| GcdBadDecr | 1 | 0 | 0 | 1 | 0 | 0 |
| GcdBadExit | 1 | 0 | 0 | 0 | 1 | 0 |
| GcdVacuous | 4 VACUOUS | 0 | 0 | 0 | 0 | 4 (probe unsat) |

`GcdVacuous.sol` adds `a < 1` to `a > 0`: solar-verify discharges every obligation and exits 0
with only a warning; the gate rejects it with exit 4, also without `--assume`
(`gate/GcdVacuous-noassume`).

## What is checked where (this commit)

- **SMT-checked only (z3 5.4.1, through solar-verify):** every row of the table above: each
  obligation's answer, the probe, the witnesses and the negatives. Nothing in this commit is
  checked by Lean: no `.lean` module is added (the emitted modules are kept as `.lean.txt`), and
  `gen_loopvc.py` is a generator whose output has not been built.
- **Lean-checked: none yet, for either contract.** The Lean modules (the kernel-decided verdict of
  each script, and Counter's binding to the source loop bridge) come in a later commit, only once
  they build. `Gcd.gcd` is SMT-checked only, and its Lean binding, MIR, bytecode and gas stay open.

## Outcomes per loop (matrix.json; exit 0 holds, 1 fails, 3 none emitted)

Initiation, consecution, termination and exit are separate solar-verify obligations with their own
ids and answers. Nonvacuity is the advisory probe (sat: some path reaches the return under the
precondition) plus a z3 model through `witness.py` that runs the loop (Counter n = 3, count = 5;
Gcd a = 12, b = 18). One negative per obligation kind fails exactly that kind (`inputs/*Bad*.sol`,
solar-verify exit 1); `GcdVacuous.sol` (a contradictory precondition) is accepted by solar-verify
with exit 0 and only a warning, so nonvacuity is gated by the probe's answer and `witness.py`'s
exit 1, not by solar-verify's exit.

Resource (gas) is not covered: solar-verify has no gas obligations, and the certify driver's bound
(`gas_need`, tools/certify/generic.py) reads a `stage_of_runs` fuel per EVM IR stage
(`shape_gen.last_stage`), which looping code does not have (its stages are proved through cut
points), so it stops with "no EVM IR stage chain to the final EVM IR" for both contracts.

## Not covered

- The binding is generated per contract: `LoopVC.lean` is written for `bump`; a generic
  `ForObl` from `ObsValid` needs a map from a loop header's `SymState` words to solar-verify's
  SSA names (which the manifest does not carry) and a general `WExpr` ↔ `Tm` evaluation lemma.
- `Gcd.gcd`: no Lean check and no source loop binding: its body branches, and `LoopErased` has
  only the straight-line `StmtRuns` forms.
- The MIR loop cut point and the bytecode side are out of scope here.
