# Proof-engine evaluation: lanes and receipts

The evaluation of Lean 4.35's Std.Do / Std.WP (vcgen) and Lean.Meta.Sym (SymM, Sym.Simp,
Sym.Apply, Sym.Grind, cbv) against the repository's own unfold-and-simplify engine. One integrator
(this branch, `alpharush/eval-symm`) owns the shared files (lakefile, `scripts/eval/`,
`Verify/Eval/Common/`, this table); each lane wrote only its own directory. Nothing here is
imported by the default build, the E-edge statements or the axiom gate. The lead (integrator)
owns every proof-engine change proposed below; lanes only measured.

Toolchain leanprover/lean4:v4.35.0, Mathlib v4.35.0, base commit 6dd035dc (PR #166 head).

## Rules every lane followed

- Same statement, assumptions, imports, toolchain and machine as the frozen baseline; baseline and
  new proof side by side, statements compared by `rfl` / `#same_statement` (lane H).
- Measured separately: elaboration/tactic time, kernel time (profiler "type checking" and
  `#kernel_recheck`), proof DAG/tree nodes (`#proof_stats`), .olean bytes, peak RSS;
  doubling ratios over fixture families of 16/32/64/128/256 ops.
- Axioms only propext, Classical.choice, Quot.sound: no native_decide, bv_decide, sorry or
  trusted SMT (audited transitively by `scripts/eval/audit/axioms.sh`).
- No speedup claim without a measurement. All runs on one shared 5 vCPU / 14 GB machine with
  other lanes running: read ratios, single timings carry about ±30% noise.

## Build admission

Every check went through `scripts/eval/check.sh <lane> <file>`: at most 2 Lean processes at
once (`LEAN_NUM_THREADS=1`, `-M 5000`), wall, peak RSS and profiler times appended to a
receipts file. Measured peak RSS per check: 0.8 to 3.8 GB (imports alone 2.5 to 2.6 GB for
Verify.* importers). Repository modules were built once by the integrator, one build at a time
(build 1: Verify.Tactic, CounterBump, Symex, 12 min 42 s, 5.4 GB peak; build 2: Verify.W1/W4,
Corpus C1 Dirty, W1Proofs.Tactic, SolarTV/Shared Word, Wide.Tactic, 2 min 54 s, 3.0 GB; build 3:
Contracts.VerifyCounter.Bump/BumpTotal, 29 s). No remote box was used.

Known non-building files (record failures on purpose or need unbuilt generated modules), excluded
from any `lake build VerifyEval`: G/Real/BumpLeaves, G/Capture/AbiHash, G/Cbv/Mulx, G/Bench,
F/ClzOld, F/CheckedExpOld (old variants that time out or get stuck by design), B/W4Pilot.
`check.sh` does not pass the lakefile's leanOptions (F/ClzOld differs for that reason).

## Receipts

Checkpoint commit: 0b25752. Results commit: 23115b99.

| Lane | Subagent | Write scope | Deps | Interface | Build admission | Status | Patch sha | Receipt |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A baseline, schema, fixtures, kernel replay | 1 | Verify/Eval/A, scripts/eval/fixtures, docs/eval/a.md | Verify.Basic, Verify.Tactic | schema.json, Fixtures/<Family><n>.stmt, Replay.lean | check.sh, ≤3.8 GB | delivered | 0b25752 | Baseline breaks before n=64 in every family (table below); generated Bump 8.8 s / 1.8 GB / kernel 1.6 s; kernel replay Bump 97 thms 978 ms; Replay rejects ill-typed and swapped terms. [a.md](a.md) |
| B Sym.Simp adapter for Wide/Tactic evalGoal | 2 | Verify/Eval/B, docs/eval/b.md | Verify.W1/W4, Wide.Tactic | wide_symex_sym beside wide_symex | check.sh, ≤3.0 GB | partial | 23115b99 | run_f and run_set proved (Sym rounds + Meta fallback), kernel and DAG within noise, no speedup (fallback rounds dominate; run_set 27.6 vs 24.6 s). Deeper Cbv-matcher variant: 1,103 Sym steps in 470 ms on run_set but different normal form, not a proof. Not run on generated VCs (none use wide_symex). [b.md](b.md) |
| C EVM backward-rule stepper | 3 | Verify/Eval/C, docs/eval/c.md | Evm.Symex, EthLib logic | evm_sym tactic, 83 fused rules | check.sh, ≤3.0 GB | partial | 23115b99 | At 256 ops: tactic 62/51 ms vs 14.4/10.2 s (Straight/Shared); Branch32–256 proved only by stepper; DAG 1.4x, kernel 561 vs 103 ms (x2.7 per doubling); generated C1 dirty theorem proved verbatim. Memory opcodes not attempted. [c.md](c.md) |
| D Std.WP / vcgen with external invariants | lead | Verify/Eval/D, docs/eval/d.md, scripts/eval/gen_*.{sh,py} | Verify.Basic, W1/W4, CounterBump | bridge loom_wp_eq_stdWP, whileM_spec | check.sh, ≤2.6 GB | delivered | 23115b99 | bump_spec proved by vcgen with the unedited Spacer invariant (4 lines, 203 ms, kernel 77 vs 9 ms); W1/W4 within noise; scaling table below; vcgen internal error at Memory128. [d.md](d.md) |
| E proof-DAG shape | 4 | Verify/Eval/E, docs/eval/e.md | Evm.Symex, Verify.Basic | shape guidance for generators | check.sh, ≤3.0 GB | partial | 23115b99 | Shared per-block lemmas: kernel 1132→341 ms at 128 blocks, 1229→781 at 256, .olean −25%; hoisting identical facts, balanced trees, frame defs: no effect. Generated Bump already per-segment. Generated modules beyond Bump not built. [e.md](e.md) |
| F library equivalences | 5 | Verify/Eval/F, docs/eval/f.md | SolarTV.Word, Shared.Word, Verify.Basic | lemmas + adoption list | check.sh, ≤2.6 GB | delivered | 0b25752 | power via Nat.powMod (old variants time out); storage write laws simp 855 ms vs 3.59 s, kernel 74 vs 209 ms; clzWord = BitVec.clz. [f.md](f.md) |
| G shared arithmetic/path facts, vc_grind, cbv | 6 | Verify/Eval/G, docs/eval/g.md | W1Proofs.Tactic, Verify.Tactic | discharger variants | check.sh, ≤3.2 GB | partial | 23115b99 | Normalize-once + omega fastest (0.69x base); shared grind 1.7x slower elaboration, 40% smaller kernel; real generated side conditions ~90% failing attempts; vc_grind Vault 17/17 vs vc_valid 14/17; cbv 2–18x slower to check than decide +kernel. Sym.Grind discharger issue on contradictory context (fails closed). [g.md](g.md) |
| H trust gate, mutations, cold replay | 7 | Verify/Eval/H, scripts/eval/audit, docs/eval/h.md | all lanes | #same_statement, axioms.sh, #mutation_check, cold_replay.sh | check.sh, ≤2.6 GB | partial (core delivered) | 23115b99 | 12/12 bad axiom fixtures rejected; 4,219 lane rows and 852 generated VerifyCounter rows clean; mutants rejected 13/13 sc_vcgen, 9/9 vcgen+sc_close, 13/13 vcgen+grind, 9/9 mvcgen, 4/4 evm_step, 9/9 sibling isolation; cold replay 178 rows match. [h.md](h.md) |
| acc4-flag generated VCs, per obligation (records d66e60bf) | lead | scripts/eval/acc4, docs/eval/acc4.md, docs/eval/acc4/ | solidity-lean 44572c15 + the record's 26 generated modules | CSVs per module, command, declaration, tactic | one lock, LEAN_NUM_THREADS=1, ≤2.93 GB | delivered | this commit | 105.9 s single-thread wall, kernel 12.9 s, 0 of 3,167 declarations rejected; top costs: sym_exec simp 30.4 s, interpreted kernel_rfl cloning 18.6 s, kernel Keccak of 4 selectors 6.6 s. [acc4.md](acc4.md) |

## Owner addenda

| Item | Owner lanes | Status | Result |
| --- | --- | --- | --- |
| Thread `Grind.Goal` through the VC/path tree (one mkGoal at the root, children extend, fork at branches, facts scoped to descendants) | B, C | C delivered, B not attempted | C's stepper threads one Goal per path, children extend the parent copy. |
| Experiment 1: persistent branch-local Grind.Goal vs fresh goal per child | C (B not attempted) | delivered (C) | At 256 ops: threaded internalizes 21 decls vs 161 fresh, 24.8 vs 50.2 ms; same proofs. |
| Experiment 2: grind's independent leaf coverage on locked exported rows | G | partial: 36 of 63 rows | Vault vc_grind 17/17 vs vc_valid 14/17 (five vacuous rows confirmed); ArrayMax 16/19 both. Bump loop leaves: grind 9/14 vs total_leaf 14/14, kernel 4x smaller where grind closes. Counter/Token exports absent. |
| Sibling-isolation negatives (contradictory sibling assumptions, one-sided conditional rewrites) | B, C, G; H audits | delivered C, G, H; B not attempted | All pass: no leak in threaded, condRewrite, eager, fresh modes (C), shared-facts discharger incl. a leaky control that is caught (G), 9/9 mutants (H). |
| vc_grind backend with vc_smt's prep, every backend on every frozen row | G | partial | Plugin-free; prep dominates cost; negatives fail for every backend. vc_smt not rebuilt here. |
| cbv pilots on bounded leaves | G, H audits | delivered | cbv/decide_cbv proofs 30–3000x larger, 2–18x slower to check; walk_eq 14 s vs 0.9 s; negatives fail for every variant. Keep decide +kernel. |
| Transitive axiom audit of every cbv/grind proof | H | delivered | No ofReduceBool, trustCompiler or user axiom. |

## Generated end-to-end VCs vs hand-written statements

Generated (produced by the repository's generators, statements unchanged): Contracts/VerifyCounter
Bump, BumpTotal, BumpWrongRank, Inferred (solar inferred.py); Corpus C1 Dirty; Verify/Discharge
frozen rows (Vault, ArrayMax). Everything else is hand-written fixtures or existing hand proofs.

| Measurement | Generated | Engine result |
| --- | --- | --- |
| Bump / BumpTotal baseline (A) | yes | 8.8 / 7.7 s wall, kernel 1.6 / 1.3 s, 97 / 83 theorems |
| BumpWrongRank must fail (A, H, G) | yes | rejected by every engine |
| Bump loop leaves, 15 captured verbatim (G) | yes | total_leaf 14/14, grind 9/14, shared grind 9/14 |
| sym_mem side conditions, 1,178 captured calls (G) | yes | ~90% speculative failures take ~95% of discharger time; ground-first 0.38–0.66x |
| C1 dirty-argument theorem (C) | yes | evm_sym ~83 ms vs ~3.1 s tactic; recheck 19.3 vs 22.9 ms |
| Frozen discharge rows (G) | yes | 36/63 rows; vc_grind ≥ vc_valid on every measured row |
| Spacer invariant for bump (D) | yes (invariant) | used unedited by vcgen; frame and pre-loop fact added |
| W1/W4, Counter bump_spec, scaling fixtures (B, C, D, E, F) | no | tables in each lane's doc |

The generic driver's own generated VC modules were not available when these runs were made, so no
engine was measured on them.

## Scaling summary (tactic or elaboration time, one run each)

| Family, n | baseline sc_vcgen/sc_close (A) | vcgen + finish (D) | evm_sym stepper (C) |
| --- | --- | --- | --- |
| Straight 16 / 32 / 64 / 128 / 256 | 6.0 s / timeout | 0.31 / 2.3 / 447 s / timeout | ok at every size, 62 ms at 256 (EVM fixture: baseline symex 14.4 s there) |
| Branch 16 / 32 / 64 | 3.8 / 7.1 s / timeout | 0.13 / 0.19 s / grind incomplete | ok 32–256, symex_one fails |
| Memory 16 / 32 / 64 / 128 | 50.2 / 5.5 / 20.4 s / maxSteps | 0.11 / 0.24 / 0.72 s / vcgen crash | not attempted |
| Shared 16 / 32 / 64 / 128 / 256 | 35.0 / 141 s / maxSteps | 0.11 / 0.18 / 0.66 / 2.0 / 10.3 s | 51 ms at 256 (EVM fixture: baseline 10.2 s) |
| LoopBody 16 / 32 | 50.7 s / OOM | not closed | n/a |

Lane C's EVM fixtures are its own (C/gen_fixtures.py) against the repository's symex tactic, not
lane A's SolM fixtures.

## Proof-engine improvements (owner: lead)

| Change | Evidence | Gate before landing |
| --- | --- | --- |
| Add bridge lemmas (D/Bridge.lean) to Verify/Basic and offer vcgen + external invariants as an alternative to sc_vcgen per contract | D | vcgen leaves experimental; #same_statement; axioms.sh |
| Hoist path-context normalization out of the per-rewrite sym_mem discharger; ground-first filter | G | cold replay of generated stages |
| grind as fallback after the existing closer where its kernel term is smaller | G | mutation check |
| Per-block / per-cut-point lemmas in generators | E | generated module rebuild |
| Library equivalences (powMod, storage write laws, BitVec.clz) | F | file:line list in f.md |
| evm_sym stepper for EthLib-frame obligations after premise proofs shrink and memory rules exist | C | mutation check, Memory family |
| vc_grind as plugin-free fallback after vc_smt in discharge.sh | G | all 63 frozen rows |
| Fix check.sh to pass lakefile leanOptions; take toKernelEnv out of #kernel_recheck's timer | H, G | none |
