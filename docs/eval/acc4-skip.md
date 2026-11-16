# sym_norm without no-progress sym_eval passes: measured on acc4-flag

Next step from [acc4-perpc.md](acc4-perpc.md): sym_exec's time is sym_norm's repeated whole-goal
passes, not block evaluation. sym_norm is `repeat (first | sym_eval | sym_cond | sym_mem)`, so
after every successful sym_eval the next round runs sym_eval again. sym_eval is one dsimp call,
which already runs to a fixpoint, so that pass can only fail, after traversing the whole goal.
The change skips exactly that pass and keeps every other step and its order. A failed tactic
leaves no proof term, so the proofs should not change, and they don't.

## Change

[sym_norm.patch](acc4/sym_norm.patch), against tv/W1Proofs/Tactic.lean at 44572c15: the
`sym_norm` macro becomes an elaborator loop with the same steps. Each round tries sym_eval (unless
the last step was sym_eval), then sym_cond, then sym_mem, and stops when none applies. No
statement, lemma set, generated file or axiom changes.

Measured two ways:
1. Bench copies (scripts/eval/acc4/skip/): `sym_exec_skip` on copies of the six generated EVM run
   proofs, only `sym_exec` → `sym_exec_skip` and the namespace changed. Passes skipped:
   Evm1 73, Evm2 45, Evm3 47, Evm4 47, Evm5 45, Sched 56.
2. The patch itself, applied to the bench worktree's W1Proofs/Tactic.lean, then `lake -R build
   -KleanMemory=6000 flag_4ce5cf9a.Final`.

## Results (one lock, LEAN_NUM_THREADS=1, -M 6000, 2 runs each; [skip_ab.csv](acc4/skip_ab.csv))

| Module | wall s, runs orig → skip | tactic+simp ms | kernel recheck ms | proof DAG nodes | peak RSS MiB |
| --- | --- | --- | --- | --- | --- |
| Evm1 | 11.27/11.70 → 9.56/9.61 | 6,995 → 5,780 | 254.5 → 254.8 | 37,991 = | 1,688 → 1,663 |
| Evm2 | 8.53/8.77 → 7.55/7.79 | 4,940 → 4,240 | 187.8 → 187.7 | 31,641 = | 1,653 → 1,635 |
| Evm3 | 7.59/8.02 → 6.58/6.77 | 4,310 → 3,525 | 140.7 → 153.8 | 27,611 = | 1,641 → 1,628 |
| Evm4 | 7.89/7.77 → 6.53/6.82 | 4,350 → 3,540 | 208.5 → 166.1 | 28,016 = | 1,642 → 1,630 |
| Evm5 | 8.17/7.80 → 7.08/6.80 | 4,420 → 3,685 | 247.6 → 193.3 | 28,643 = | 1,648 → 1,625 |
| Sched | 12.50/12.51 → 11.23/11.40 | 7,855 → 7,155 | 359.1 → 324.8 | 39,630 = | 1,695 → 1,677 |

Wall includes the category profiler and imports (about 3.5 s per module); compare rows.

- Wall: every module is 1.0–2.1 s faster in both runs, against a spread of at most 0.43 s between
  repeats of one mode. In all: 54.97 → 47.36 s per pass of the six (−14%), tactic+simp 32.9 → 27.9 s
  (−15%). Six sizes, 45–73 skipped passes; no scaling claim beyond them.
- Kernel: the proof terms are the same (below), so the kernel checks the same terms. The recheck
  differences (−54 to +13 ms) are run-to-run noise on identical input.
- Peak RSS: 12–25 MiB lower.

## Identity checks

- Statements: all six types are `==` to the originals ([compare_skip.csv](acc4/compare_skip.csv)).
- Proof values: `==` to the originals for all six once the copies' namespace prefix (.SK) is mapped
  back. The only raw difference is the names of the aux `_simp_` lemmas, and those 30 lemmas are
  themselves identical in type and value.
- rep1 == rep2: each mode's two direct builds give byte-identical oleans (skip_ab.csv).
- With the patch applied to W1Proofs/Tactic.lean, all 23 Lake-built oleans of the generated modules
  (Runs, Stages, Shape, Statement, Lowering, SpecConnect, Final, …) are byte-identical to before
  ([olean_identity_skip.txt](acc4/olean_identity_skip.txt)). The repository modules that use sym_exec
  and were rebuilt (SolidCore.Refinement.Solar Bank/Events/MulX Certified, Totality, Verify.ShapeGeneric,
  ShapeSpecExport) still build.
- Axioms: #axioms_within passes in every copy; the patch adds none.

## Gate: integrate

All three conditions hold: statements identical, kernel/proof check identical (same proof terms,
byte-identical oleans), and a wall gain beyond noise. Integration path: apply
docs/eval/acc4/sym_norm.patch to tv/W1Proofs/Tactic.lean on the RC branch, by that file's owner, then
`lake build`; the generated oleans should be byte-identical, as here.
