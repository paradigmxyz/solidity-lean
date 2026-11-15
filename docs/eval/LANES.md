# Proof-engine evaluation: lanes and receipts

The evaluation of Lean 4.35's Std.Do / vcgen and Lean.Meta.Sym (SymM, Sym.Simp, Sym.Apply,
Sym.Grind) against the repository's own unfold-and-simplify engine. One integrator (this branch,
`alpharush/eval-symm`) owns the shared files (lakefile, CI, `scripts/eval/`,
`Verify/Eval/Common/`); each lane writes only its own experiment directory. Nothing here is
imported by the default build, the E-edge statements or the axiom gate.

Toolchain leanprover/lean4:v4.35.0, Mathlib v4.35.0, base commit 6dd035dc (PR #166 head).

## Rules every lane follows

- Same statement, assumptions, imports, toolchain and machine as the frozen baseline; baseline and
  new proof side by side in one file.
- Measured separately: elaboration/tactic time, kernel time (profiler "type checking" and
  `#kernel_recheck`), proof DAG/tree nodes (`#proof_stats`), .olean bytes, peak RSS, heartbeats;
  doubling ratios over fixture families of 16/32/64/128/256 ops.
- Axioms only propext, Classical.choice, Quot.sound: no native_decide, bv_decide, sorry or
  trusted SMT.
- No speedup claim without a measurement.

## Build admission

Every check goes through `scripts/eval/check.sh <lane> <file>`: at most 2 Lean processes at once
on the 14 GB Hand (`LEAN_NUM_THREADS=1`, `-M 5000`), each run's wall time, peak RSS and profiler
times appended to a receipts file. Repository modules are built once by the integrator
(`lake build -KleanMemory=4500`, one build at a time); lanes never run `lake build`. The box pool
(org cap 3 active boxes) was full when the lanes started; heavy builds move there when a slot frees.

## Receipts

| Lane | Subagent | Write scope | Deps | Interface | Build admission | Status | Patch sha | Receipt |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A baseline, schema, fixtures, kernel replay | 1 | Verify/Eval/A, scripts/eval/fixtures, docs/eval/a.md | Verify.Basic, Verify.Tactic | schema.json, Fixtures/<Family><n>.stmt, Replay | check.sh slot | dispatched | | |
| B Sym.Simp adapter (Wide/Tactic evalGoal) | 2 | Verify/Eval/B, docs/eval/b.md | Verify.W1, Verify.W4, Wide.Tactic | experimental tactic beside wide_symex | check.sh slot | dispatched | | |
| C EVM backward-rule stepper | 3 | Verify/Eval/C, docs/eval/c.md | Evm.Symex, EthLib Logic | stepper tactic + fused rules | check.sh slot | dispatched | | |
| D Std.Do / vcgen with external invariants | lead | Verify/Eval/D, docs/eval/d.md | Verify.Basic, Verify.W1/W4, Verify.CounterBump | bridge lemma Loom wp = Std.Do wp | check.sh slot | in progress | | |
| E proof-DAG shape | 4 | Verify/Eval/E, docs/eval/e.md | Evm.Symex, Verify.Basic | shape guidance for generators | check.sh slot | dispatched | | |
| F library equivalences | 5 | Verify/Eval/F, docs/eval/f.md | SolarTV.Word, Shared.Word, Verify.Basic | lemmas | check.sh slot | dispatched | | |
| G shared arithmetic/path facts | 6 | Verify/Eval/G, docs/eval/g.md | W1Proofs.Tactic, Verify.Tactic | discharger | check.sh slot | dispatched | | |
| H trust gate, mutations, cold replay | 7 | Verify/Eval/H, scripts/eval/audit, docs/eval/h.md | all lanes' outputs | audit + mutation harness | check.sh slot | dispatched | | |

## Owner addenda folded into existing lanes

| Item | Owner lanes | Status |
| --- | --- | --- |
| Carry `Lean.Meta.Grind.Goal` (not a bare MVarId) through the VC/path tree: one `mkGoal` at the common root, `Goal.apply` children, `internalizeAll` of new hypotheses, fork at branches, facts scoped to descendants | B (source evaluator), C (EVM paths) | dispatched |
| Experiment 1: persistent parent session with branch-local Grind.Goal vs fresh goals per child, measuring inherited-context internalization cost and sibling isolation on the scaling fixtures | B, C (H checks) | dispatched |
| Experiment 2: grind's independent leaf coverage on the locked exported discharge rows (one process per row; sharing only by rebuilt common prefixes or checked summary lemmas) | G (H checks) | dispatched |
| Sibling-isolation negative test: contradictory assumptions in sibling branches and one-sided conditional rewrite side conditions; must fail on any leak | B, C, G; H audits | dispatched |
| `vc_grind` backend with `vc_smt`'s prep/normalization, solver-independent normalization split from the module importing Smt, every backend run on every frozen row (LIA/EUF, then quantified arrays, nonlinear, bitvectors); grind failure = unknown, never sat; cvc5 model check kept | G | dispatched |
| cbv pilots on bounded leaves (Sat/Ground.lean, test/sat tiny/b8, mulx Assembly items_eq/walk_eq): decide +kernel vs decide_cbv vs cbv vs the current proof on identical statements; no blanket cbv, opaque interpreter boundaries kept, negatives unchanged | G measures, H audits | dispatched |
| Transitive axiom audit of every cbv/grind proof; native_decide and the stock BV certificate path rejected | H | dispatched |

