# acc4-flag: cost of the generated VCs, per obligation

What the accepted positive acc4-flag (records branch alpharush/t1-generic-records at d66e60bf)
costs to check, measured per obligation on its own generated modules. Nothing here changes the
driver, the generated files or any proof; the numbers are for choosing what to make cheaper next.

## Method

- Inputs: solidity-lean 44572c15 (the record's base) in a separate worktree, with the record's
  26 generated modules (Certified/flag_4ce5cf9a, unedited) and the record's own lakefile
  (replay/inputs/lakefile.lean). Toolchain leanprover/lean4:v4.35.0, Mathlib from the cache.
- Machine: one hosted 5 vCPU / 14 GB Linux machine, nothing else running. Every Lean process
  went through one lock (slot.sh) with LEAN_NUM_THREADS=1. The import closure was built
  once (lake build of the 22 modules the generated files import: 2,758 jobs, 20 min 36 s,
  4.3 GB peak).
- Three passes per module, in import order (docs/eval/acc4/modules.txt):
  1. run.sh: lake -R build of the module, then a measured re-elaboration with
     trace.profiler (threshold 1 ms, --json) for attribution to commands and tactics, then
     Kernel.lean, which re-adds every constant the module declares to the kernel alone (kernel
     environment built before the timer) and records its proof size: DAG after ShareCommon
     and tree (capped at 10^7).
  2. plain.sh: an unprofiled re-elaboration with the package's options and the category
     profiler, under memtime.py (wall, peak RSS sampled from /proc every 50 ms). Wall and RSS
     come from this pass only; tracing adds up to 10 s of message formatting per module.
  3. parse_cmds.py / parse.py: join the passes into CSVs.
- The profiled pass's only errors are the #guard_msgs axiom checks, which also see the profiler's
  trace lines; the unprofiled pass exits 0 on all 26 modules, axiom checks included.
- One run per cell. Expect ±10% on repeated runs.

## Files

| File | One row per |
| --- | --- |
| [acc4_modules.csv](acc4/acc4_modules.csv) | module: wall, peak RSS, profiler categories (import, tactic execution, type checking = kernel, simp, interpretation) |
| [acc4_commands.csv](acc4/acc4_commands.csv) | command, i.e. obligation (theorem, kernel_rfl, def): elaboration ms, kernel ms during the build, kernel recheck ms, DAG and tree nodes, top 3 tactics; waits_on_proof=1 marks #axioms_within / #guard_msgs, which only wait for the proof and must not be added |
| [acc4_obligations.csv](acc4/acc4_obligations.csv) | declaration (3,167, 1,378 theorems): kernel recheck ms, DAG, tree, type DAG, status (0 rejected) |
| [acc4_tactics.csv](acc4/acc4_tactics.csv) | module and top-level tactic: profiled ms |

## Totals (single thread, unprofiled)

| | |
| --- | --- |
| 26 modules, wall | 105.9 s |
| peak RSS, largest module | 2.93 GB (Lowering) |
| kernel (type checking) | 12.9 s; recheck alone 11.2 s |
| interpreted elaborator code | 20.2 s, of which 18.6 s in Lowering and SpecConnect |
| tactic execution | 13.6 s reported, plus async proof work reported as blocked: the 7 run proofs spend 30.4 s in sym_exec (profiled) |
| imports | 12.4 s (0.5 to 0.9 s per module) |

| Module | wall s | peak RSS MiB | kernel s | interpreted s | what dominates |
| --- | --- | --- | --- | --- | --- |
| Lowering | 17.6 | 2,930 | 8.15 | 7.84 | 4 selector Keccak checks 1.6–1.8 s each; shape_eq clones |
| SpecConnect | 16.7 | 2,784 | 3.28 | 10.80 | deploy_eq clones; lower/raise erase checks 0.7 s each |
| Proofs.Runs.Sched | 8.2 | 1,698 | 0.21 | 0.21 | sym_exec 6.4 s |
| Proofs.Runs.Evm1 | 7.7 | 1,690 | 0.18 | 0.19 | sym_exec 6.1 s |
| Proofs.Runs.Evm2/3/4/5 | 5.3–5.9 | ≤1,650 | 0.09–0.12 | ≤0.17 | sym_exec 3.6–4.0 s each |
| Proofs.Runs.Stage0 | 4.7 | 1,639 | 0.15 | 0.08 | sym_exec 2.9 s |
| 19 others | 1.2–2.9 each | ≤2,714 | ≤0.31 | | imports; Shape's decide 1.4 s |

## Top 3 cost centres

1. **sym_exec's simp in the seven run proofs: 30.4 s of elaboration, 0.9 s of kernel.** Inside it,
   the per-step dsimp only [iterate_mk, iterate_zero, listLookup, …] runs 772 times for 14.6 s
   (about 19 ms per step, flat over a run, so the cost is the step itself, not a growing context),
   and simp only [*, apply_calldataload …, Mem.load_* …] runs 448 times for 11.4 s. Proof terms
   are small as DAGs (28k–40k nodes) but over 10^7 as trees. Next step: on evm1_run, same
   statement, replace the per-step whole-goal dsimp with per-pc fetch/decode equations emitted
   with the program (one rewrite per step instead of unfolding the instruction table), and
   measure elaboration, kernel and DAG against this row. The EVM backward-rule stepper measured
   in docs/eval/c.md is the fallback design if a lemma table alone does not move it.
2. **kernel_rfl clone construction runs in the interpreter: 18.6 s.** kernel_rfl shape_eq and
   kernel_rfl deploy_eq take 8.7 s each, but their kernel checks are 0.84 s and 0.80 s.
   Rerunning the same cloneRootSubst call under fresh names (BenchClone.lean) builds 297
   copies in 7.66 s, about 0.4 s of it kernel. The module profiles put the rest under
   "interpretation": the clone code in SolidCore.Refinement.Kernel/KernelRfl runs interpreted.
   Also, SpecConnect builds 1,510 copies, and 890 of them share a name suffix with copies
   Lowering already made (BenchCopies.lean), because the second using list gives them a new
   prefix. Next step: build those two modules with precompileModules (native code for the
   elaborator only; the kernel still checks every copy, so trust is unchanged) and measure
   Lowering and SpecConnect again. Reusing Lowering's copies that reach none of SpecConnect's
   extra replacements comes after that.
3. **Kernel evaluation of Keccak-256 for the four selectors: 6.6 s of Lowering's 8.15 s
   kernel.** selSig0..3_eq are kernel_rfl of selectorFromSignature on a literal signature,
   1.61–1.77 s each with 5-node proof terms: all of it is kernel reduction, and it scales with
   the number of selectors and events. Next step: prove a kernel-friendly Keccak equal to the
   current one (Nat/BitVec operations the kernel accelerates, as in docs/eval/f.md's library
   equivalences), and time selSig0_eq with it.

Smaller: Shape's three decide checks of gas bounds (0.32 s each); SpecConnect's lower/raise
erase checks (0.73 s kernel each); imports, 0.5–0.9 s per module, 12.4 s in all.

## Reproduce

    git worktree add ~/bench/sl 44572c15
    # copy Certified/record/acc4-flag/generated/Certified/flag_4ce5cf9a and
    # replay/inputs/lakefile.lean from d66e60bf into it, copy scripts/eval/acc4 to ~/bench/harness
    (cd ~/bench/sl && lake exe cache get && lake build <the 22 imports>)
    python3 ~/bench/harness/order.py > /dev/null   # run in ~/bench/sl; writes ~/bench/order.txt
    ~/bench/harness/run.sh $(cat ~/bench/order.txt)
    ~/bench/harness/plain.sh $(cat ~/bench/order.txt)
    python3 ~/bench/harness/parse_cmds.py ~/bench/out $(cat ~/bench/order.txt)
    python3 ~/bench/harness/parse.py ~/bench/out $(cat ~/bench/order.txt)
