# Per-PC equations for sym_exec: measured on acc4-flag

Cost centre 1 of [acc4.md](acc4.md) is sym_exec's evaluation in the generated run proofs. The
proposed fix was per-PC equations: evaluate each program point once instead of unfolding the
instruction semantics again on every pass. This measures that fix on the same generated VCs
(records d66e60bf, base 44572c15). **Result: it removes no measurable time, because evaluating
the blocks is only 2–5% of sym_exec's time.** No change is proposed for integration.

## What was built (bench only, nothing on an RC path changes)

- scripts/eval/acc4/perpc/Entry.lean: a pre-dsimproc on `EVM.Program.exec o call b instrs stack s`.
  The first time a path enters block `b` with a literal instruction list and an n-word literal stack,
  it evaluates `exec o call b instrs [x₁…xₙ] s` once over fresh variables with sym_eval's own dsimp
  set, abstracts the result over `o call x₁…xₙ s`, and stores it as that block's equation for that
  entry height. Later entries with the same key (another path, or the other program with an identical
  block) instantiate it. The rewrite is definitional like every sym_eval step: no lemma or axiom is
  added, and the kernel still checks the unfolding.
- scripts/eval/acc4/perpc/Tactic.lean: `sym_exec_pc`, sym_exec with that one entry added to sym_eval.
- scripts/eval/acc4/perpc/Runs/*.lean: the six generated EVM run proofs (Evm1–5, Sched), copied with
  only `sym_exec` → `sym_exec_pc` and the namespace (and so the #axioms_within message) changed.

## Results (one lock, LEAN_NUM_THREADS=1, -M 6000, 2 runs each, means; [perpc_ab.csv](acc4/perpc_ab.csv))

| Module | wall s orig → pc | tactic+simp ms | kernel recheck ms | proof DAG nodes | peak RSS MiB | block entries (from cache / evaluated / eval ms) |
| --- | --- | --- | --- | --- | --- | --- |
| Evm1 | 11.45 → 11.59 | 6,975 → 7,015 | 292 → 280 | 37,991 = | 1,667 → 1,671 | 0 / 22 / 258 |
| Evm2 | 8.77 → 9.18 | 4,975 → 5,235 | 205 → 196 | 31,641 = | 1,625 → 1,630 | 0 / 12 / 263 |
| Evm3 | 8.19 → 8.19 | 4,570 → 4,635 | 148 → 144 | 27,611 = | 1,619 → 1,623 | 1 / 10 / 183 |
| Evm4 | 7.88 → 8.29 | 4,390 → 4,635 | 144 → 165 | 28,016 = | 1,620 → 1,624 | 2 / 10 / 205 |
| Evm5 | 8.31 → 8.39 | 4,550 → 4,530 | 167 → 165 | 28,643 = | 1,621 → 1,622 | 1 / 9 / 225 |
| Sched | 12.14 → 13.02 | 7,645 → 8,445 | 347 → 375 | 39,630 = | 1,672 → 1,679 | 0 / 14 / 116 |

Wall here includes the category profiler and imports (about 3.5 s per module); compare rows, not with acc4.md's unprofiled pass.

- Six module sizes (9–22 block entries, DAG 28k–40k): no row improves beyond run-to-run spread
  (up to ±0.5 s wall); Sched and Evm2 are slightly slower (the extra instantiation pass). No
  scaling claim is made from six points.
- Reuse is nearly zero: 4 of 81 block entries recur with the same block and stack height, because
  each path enters different blocks and the two programs number their blocks differently.
- Evaluating every block entry costs 116–263 ms per module, against 4.4–7.6 s of tactic time. So
  per-PC equations in any form (cached, or fused per-instruction lemmas) can save at most that
  2–5%. The rest is sym_norm's repeated whole-goal passes: each `repeat (first | sym_eval | sym_cond | sym_mem)`
  round and each split re-traverses the whole goal, and ends with three passes that make no progress.

## Identity checks

- Statements: all six theorems' types are `==` to the originals' (scripts/eval/acc4/ComparePC.lean,
  [compare_perpc.csv](acc4/compare_perpc.csv)). Proof values differ (different intermediate casts),
  with the same DAG size and kernel time within noise. Every auxiliary `_simp_` lemma is identical.
- Determinism: each mode's two direct builds give byte-identical oleans (sha256 in perpc_ab.csv).
- Untouched modules: the generated modules are not edited; Lowering and SpecConnect oleans match the
  hashes recorded in [acc4-native.md](acc4-native.md) (9dee0d55…, 291e2696…). Lake-built and direct-built
  oleans of the same file differ (Lake passes the package options), so comparisons are within one mode.
- Axioms: #axioms_within passes in every copy (propext, Classical.choice, Quot.sound).

## Next step this points to

Cut no-progress passes rather than evaluation: measure how many sym_eval/sym_cond/sym_mem calls in
sym_norm fail after a full traversal, and try one variant that runs sym_eval only after sym_cond or
a split changed the goal. A failed pass leaves no proof term, so the proof stays the same.
