# Loop route: solar-verify's loop obligations, bound to Counter's source semantics

Everything here is pinned in `MANIFEST.json` and replayed from a clean checkout by
`replay.sh` (see the end). Two loops:

- `inputs/Counter.sol`, `Counter.bump`: a `for` loop over a storage counter.
- `inputs/Gcd.sol`, `Gcd.gcd` (held out, not Counter-shaped): a `while` loop with a `!=` guard, a
  branching body that writes one of two locals, a sum as its measure, and no storage.

Pins: compiler solar `fd53f637ef69065f897a1760726c254ccd7f9aa2`
(`0.8.38+commit.fd53f637.solar.0.3.0-dev`), whose `--emit-loop-heads` wrote the loop-head map
`Counter/Counter.loop-heads.json` (sha256 `f4cc0bcf…`); z3 5.4.1; Lean 4.35.0; solidity-lean base
`44572c15` with the source loop bridge `0e88f235`. The VC script is the same bytes as the earlier
c09510a3 run (`smt_sha256` `2c92f3bc…`); only the compiler string differs, so the VCs were
re-emitted on fd53f637 to match the map's pin rather than relaxing the check.

## What is checked where

| | Counter.bump | Gcd.gcd |
|---|---|---|
| obligations discharged by z3 (solar-verify) | yes | yes |
| script verdict decided by the Lean kernel, no solver (`RC/<C>/Obligations.lean`, `obs_valid`) | yes | yes |
| obligations bound to the source semantics in Lean (`Contracts/VerifyCounter/LoopVC.lean`) | yes | **OPEN** |
| MIR loop cut point | **OPEN** | **OPEN** |
| bytecode | **OPEN** | **OPEN** |
| gas / fuel bound | **OPEN** | **OPEN** |

## The Counter binding

- `Verify/LoopSource/gen_loopmap.py` reads the loop-head map and rejects it (exit 3) unless its
  format, compiler, `dry_run`/`strict`, function and source hash (recomputed from the file) equal the
  obligations'; `solar-verify --check-loop-heads` rejects a map the source no longer gives. It
  writes `RC/Counter/Map.lean`: `M` places `count@27` (slot 0 at the head), `count@17` (slot 0 at
  entry), `i@28` and `n@21` (in scope); `freeNames` lists the names the map does not place
  (`limit@18`, which the loop does not mention, and `this`, `msg.sender`, `msg.value`), whose values
  the binding supplies (`frN`), with the obligations' facts still checked at them.
- `Verify/LoopSource/LoopMap.lean`: `LoopMap.env` (solar-verify's assignment from the map at a
  header valuation), `Corr` and `Corr.eval` (an SMT term over the names evaluates to the word
  expression it denotes where nothing wraps), `holds_eq`/`holds_le`/`holds_lt`.
- `Contracts/VerifyCounter/LoopVC.lean`: `w_count17`, `w_n21`, `w_i28`, `w_count27` check by
  `decide` that the map's places are the words of the source loop header `headerS` (a wrong map
  fails here); `init_vc`, `consec_vc`, `decr_vc`, `post_vc` take initiation, consecution, the
  measure's fall and the exit from solar-verify's obligations at `envN`; `consec_corr` ties
  consecution's goal to the body tree's slot write and `i` update; `pre_witness` is a satisfiable
  precondition (n = 3, count = 5, limit = 8) at which consecution's facts hold.
- **Expected headline, stated apart:** `RC/Headline.lean` defines `CounterBumpLoopHeadline` importing only
  the source semantics and Counter's source model (its build checks that none of the proof or
  obligation modules is imported); `RC/HeadlineCheck.lean` checks
  `example : CounterBumpLoopHeadline := Contracts.VerifyCounter.LoopVC.body_runs_vc` in the kernel, and
  the replay checks that a changed statement (fuel bound `2 ^ 256 + 7`) does not check.
- **Headline:** `body_runs_vc : ∀ ev tbl fn, fn.body = bumpBody → initState fn = S0 → ∀ fuel,
  2 ^ 256 + 8 ≤ fuel → Loop.BodyRuns (env ev tbl) fuel fn bumpBr`, axioms `propext`,
  `Classical.choice`, `Quot.sound`; `RC/Receipt.lean` checks these axioms for every theorem above
  and that `body_runs_vc` rests on `Counter.obs_valid`, `Counter.M` and `Counter.script`.
- Not from solar-verify: the overflow guards of `count++` and `i++`, proved in Lean from the
  invariant and the precondition (solar-verify outside `--strict` treats overflow as a revert).

## Acceptance gate (SMT side)

`Verify/LoopSource/loopgate.py`: each outcome apart, nonvacuity required (exit 0 ACCEPT, 1 an
obligation failed, 3 a loop kind missing, 4 VACUOUS). Counter and Gcd exit 0; the eight one-line
negatives (`inputs/*Bad*.sol`) exit 1 on exactly their kind; `GcdVacuous.sol` (`a > 0 && a < 1`)
exits 4 although solar-verify itself exits 0 on it.

## Replay

```
cargo build -p solar-verify   # in solar at fd53f637
LEAN_NUM_THREADS=1 bash Verify/LoopSource/RC/replay.sh <solar-verify> <z3> <out-dir>
```

It checks the pinned hashes, re-emits the VCs and the loop-head map and compares them with the
committed files and `MANIFEST.json`, regenerates every generated Lean module and compares bytes,
builds `Verify.LoopSource.RC.Receipt`, and runs the negatives: a stale compiler or source hash
(`gen_loopmap.py` exit 3), an edited source (`--check-loop-heads` exit 1), a map with the wrong
slot or a swapped variable (Lean exit 1), and the gate cases. `replay.json` records the result and the resource admission (wall time and peak
RSS of the whole replay against an 8 GiB / 3600 s budget).

Scope: this closes only the Counter source-consumer edge. MIR, bytecode and gas stay OPEN; there is
no end-to-end claim.
