# Lane C: a SymM backward-rule EVM stepper

Status: delivered (partial on generated VCs, see the addenda table). Toolchain v4.35.0, base 6dd035dc.
All checks ran through `scripts/eval/check.sh C …` (receipts in `~/eval-receipts.jsonl`, logs in
`~/eval-logs/*-C-*.log`).

## What was built

| File | What |
| --- | --- |
| `Verify/Eval/C/gen_rules.py` → `Rules.lean` | 83 fused one-opcode rules over a code stored as one number (`NatCode.ofNat n size`): each is EthLib's rule for the opcode with `Triple.seq` already applied, concluding `Hoare .fusaka (At (ofNat n size) msg pc stack mem gas st ss rd) R` for any `R`. Premises are facts on literals (`pc + k < size`, `n >>> (8 * (size - 1 - pc)) % 256 = byte`, PUSH data as a `BitVec.ofNat` of a shift/mod), gas (`c ≤ gas`), stack room, and for jumps `walk n size size 0 d = true` plus the JUMPDEST byte. DUPk/SWAPk match explicit cons cells, so no premise indexes a list. JUMPI has three rules: `step_jumpi_zero` / `step_jumpi_taken` (a premise decides) and `step_jumpi_split` (Symex's `jumpi_split` over a NatCode: both continuations, each under its path condition). Terminal rules: REVERT of 0 bytes (`Reverted` or `Done`), STOP (`Done`), and `at_close` (reach a stated frame). |
| `Verify/Eval/C/Stepper.lean` | `evm_sym [code eqns] (using [rewrites])?`: a SymM/GrindM driver. Reads the opcode byte off the literal code number only to pick the rule; applies it with `Sym.BackwardRule.apply` (via `Grind.Goal.apply`); proves every premise (Sym.simp with `evalGround` + `simpControl` + 4 rewrite rules; assumption; kernel-evaluated `Eq.refl true` for `walk` after evaluating it in meta code; else `grind` in the goal's own state); normalizes the next frame with Sym.simp whose persistent cache is threaded through the whole run. Options: `verify.eval.c.fresh` (experiment 1 control), `eager` (refute every split child), `shareCache`, `condRewrite` (ISZERO conditional rewrites discharged by grind through `Goal.mkSymSimpDischarger`), `stats`, `debug`. |
| `Verify/Eval/C/W1.lean` | the two W1 targets, each a `def` proved by the baseline and by `evm_sym` |
| `Verify/Eval/C/Isolation.lean` | sibling-isolation negative tests (`#guard_msgs` pins the one open path) + positive controls |
| `Verify/Eval/C/gen_fixtures.py` → `Fix/*` | scaling fixtures: Straight, Shared (repeated subterms), Branch (decided + genuine splits), 16…256 opcodes; `<K><N>Stmt.lean` holds the statement once, `Base`/`Sym` prove it |
| `Verify/Eval/C/GenC1.lean` | pilot on a generated end-to-end VC (c1's dirty-argument theorem) |
| `run_fixtures.sh`, `summarize.py` | runner (one check.sh slot at a time) and summary |

## Soundness notes

* The byte read in meta code only selects a rule; the rule's own premise re-proves the byte.
* Infeasible branches are closed only by a proof: the E-graph finding the internalized path
  condition inconsistent (grind's `closeGoal` assigns a `False.elim` proof), `grind` on `False` in
  the branch's own state, or `exfalso; symex_omega` (Symex's kernel-checked bv_omega chain).
  `simpControl` only selects `ite` branches whose condition evaluates to a literal.
* `walk` premises get `Eq.refl true`, checked by the kernel by evaluation (what `decide +kernel` does).
* No `bv_decide`, `native_decide` or `sorry` in the stepper's proofs; `#print axioms` is in each file.


## Results (handwritten targets and fixtures)

All rows: `scripts/eval/check.sh C`, `LEAN_NUM_THREADS=1`, `-M 5000`, one Lean process per file.
Wall times include ~1.1 s import and the `#proof_stats`/`#kernel_recheck` commands of the file
(the stepper's meta code and `Measure`'s commands run in the interpreter: "interpretation" ~2.1 s).
"kernel" is the profiler's type-checking time for the file; "recheck" is `#kernel_recheck` of the
one theorem. The stepper's own counters (`-Dverify.eval.c.stats=true`) split its time into rule
construction / Sym.apply / Sym.simp / premise discharge / internalize / grind. The profiler does not
attribute the stepper's elaborator to "tactic execution", so for the stepper the counters are the
tactic-time measurement.

### W1 targets (handwritten statements over solar's generated W1 bytecode)

Log 20261115T043022-C-W1 (exit 0), file `Verify/Eval/C/W1.lean`.

| statement | proof | result | proof DAG (tree) | kernel recheck | stepper counters |
| --- | --- | --- | --- | --- | --- |
| `straightStmt` 0x1a→0x24, symbolic gas `100 ≤ g` | `evm_step` ×7 + `reshape` | ok | 2229 (93.7k), aux 4845 | 6.7 ms | — |
| `straightStmt` | `evm_sym` | ok, axioms propext/choice/Quot.sound | 4547 (185.6k) | 20.6 ms | 8 steps, 27 premises, 8 gas premises by grind (24 ms) |
| `branchStmt` pc 0 → REVERT, symbolic msg | `symex_one` loop | **fails** (stops at the first JUMPI, see below) | — | — | — |
| `branchStmt` | `evm_sym` | ok, 3 axioms | 10100 (452.6k) | 18.5 ms | 43 steps, 4 splits, 5 leaves, 2 infeasible leaves refuted by grind in the branch state, 4 `walk` premises by kernel evaluation |

Baseline failure on `branchStmt`: `all_goals repeat symex_one [..] [] hfork` leaves the goal at
pc 3 (JUMPI on `msg.value`). `jumpi_split` with the same side tactics applies by hand (log
20261115T042932-C-W1); the split alternative of `symex_one` runs `exfalso; symex_bv` on each branch,
and `bv_omega` on the disjunctive hypothesis hits the recursion limit, a runtime exception that
`try`/`first` do not catch. The stepper hit the same limit when it fell back to `symex_omega` and
when `assumption` unified a path condition by default-transparency unfolding of 256-bit words; both
are now guarded (runtime exceptions caught, `assumption` at reducible transparency).

### Scaling fixtures (handwritten synthetic NatCode programs)

Straight: PUSH1 ADD SWAP1 PUSH1 XOR SWAP1 DUP2 POP repeated; Shared: DUP1 PUSH1 ADD ADD repeated
(tree size doubles every 4 opcodes); every program ends PUSH1 0 PUSH1 0 REVERT; statement
`Spec .fusaka (At code msg 0 [x, y] .empty 10000000 st ss .empty) Reverted`; baseline `repeat evm_step`
+ `revert_empty`. Concrete gas, so every premise is ground.

| fixture | base wall s | base tactic ms | base kernel ms | base recheck ms | base DAG | sym wall s | sym kernel ms | sym recheck ms | sym DAG | sym stepper ms (rules/apply/simp/discharge) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Straight16 | 3.78 | 1140 | 43 | 7.5 | 2906 | 2.35 | 4.6 | 4.3 | 3803 | 23.5/0.8/2.2/1.1 |
| Straight32 | 4.43 | 1780 | 67 | 11.4 | 5335 | 2.42 | 12.4 | 8.9 | 7291 | 24.7/2.4/4.0/2.2 |
| Straight64 | 6.43 | 3280 | 133 | 19.9 | 10202 | 2.67 | 17.0 | 18.0 | 14278 | 24.6/3.3/6.4/3.7 |
| Straight128 | 11.12 | 6920 | 298 | 42.0 | 19907 | 3.29 | 37.7 | 39.4 | 28233 | 29.6/6.3/11.7/6.9 |
| Straight256 | 21.60 | 14400 | 561 | 101.1 | 39374 | 4.40 | 103 | 74.3 | 56176 | 43.0/14.5/29.1/18.9 |
| Shared16 | 3.51 | 799 | 31 | 6.1 | 2953 | 2.24 | 5.5 | 4.7 | 3985 | 24.4/0.8/2.2/1.1 |
| Shared32 | 4.29 | 1510 | 81 | 25.1 | 5409 | 3.36 | 12.3 | 9.7 | 7558 | 27.5/1.7/3.7/2.1 |
| Shared64 | 7.33 | 2550 | 128 | 20.6 | 10329 | 3.81 | 18.8 | 19.0 | 14717 | 24.5/3.2/6.4/3.7 |
| Shared128 | 9.84 | 4740 | 247 | 50.9 | 20151 | 4.06 | 48.9 | 37.1 | 29026 | 23.7/6.0/11.7/7.0 |
| Shared256 | 17.64 | 10200 | 538 | 75.6 | 39826 | 4.71 | 126 | 111.7 | 57657 | 25.5/12.5/24.3/14.5 |

Doubling ratios 128→256: baseline tactic time ×2.08 (Straight) / ×2.15 (Shared), kernel ×1.88 /
×2.18; stepper apply+simp+discharge ×2.5 / ×2.1 (25→62 ms, 25→51 ms), kernel ×2.7 / ×2.6.
Both scale about linearly in steps. The stepper's elaboration work per step is ~0.25 ms against
the baseline's ~56 ms (`evm_step` re-runs `simp only [code eqns, …]` on each premise and `simp` on
the frame); its proof terms are ~1.4× larger as DAGs (each premise carries a Sym.simp proof over the
code literal), and its file-level kernel time grows faster per doubling (×2.7 vs ×1.9) from a
4-10× lower start. The Shared family (exponential tree, linear DAG) behaves like Straight for both:
neither engine unshares the frame.

Memory (MSTORE/MLOAD) fixtures: not attempted. EthLib has the rules (`mstore`, `mload`) and
read-over-write lemmas (`loadWord_memoryWrite_wordBytes`, `memoryReadBytes_memoryWrite*`), but the
rules carry `extendMemory`/`memoryExtend` cost and size terms that need their own fused forms with
memory-size premises; there was no time to build and measure them.


### Branch fixtures (handwritten synthetic) and experiment 1 (threaded vs fresh grind goal)

Branch: blocks CALLVALUE PUSH2 r JUMPI (decided by `msg.value = 0`) and PUSH1 off CALLDATALOAD PUSH2
r JUMPI (genuine split on a call-data word), 2:1; taken jumps share one REVERT block. Offsets cycle
(`(off + 32) % 224`), so from 128 opcodes on a repeated word's JUMPI is decided by the earlier path
condition (an assumption): splits stay at 7 and "decided" grows. Baseline `symex_one` (with `[hv]`).

| N | base | sym threaded: wall s / kernel ms / recheck ms / DAG | splits / decided / leaves | internalize: calls / decls / ms | fresh: decls / internalize ms / recheck ms | eager (refute every split child): grind ms |
| --- | --- | --- | --- | --- | --- | --- |
| 16 | ok (no split; 4.45 s, recheck 9.8 ms) | 2.63 / 4.3 / 4.3 / 3050 | 0 / 2 / 1 | 1 / 7 / 26.9 | — | — |
| 32 | **fails** at the first split (pc 16) | 2.56 / 14.4 / 12.1 / 8316 | 2 / 5 / 3 | 5 / 11 / 18.9 | 41 / 24.9 / 16.1 | 25.9 (0 refuted) |
| 64 | fails (same) | 3.09 / 32.3 / 25.0 / 16897 | 5 / 12 / 6 | 11 / 17 / 22.7 | 107 / 39.0 / 29.3 | 70.0 (0 refuted) |
| 128 | fails (same) | 2.92 / 63.9 / 50.0 / 32360 | 7 / 29 / 8 | 15 / 21 / 22.5 | 161 / 48.7 / 50.6 | 93.8 (0 refuted) |
| 256 | fails (same) | 4.12 / 335 / 202.5 / 60620 | 7 / 67 / 8 | 15 / 21 / 24.8 | 161 / 50.2 / 111.5 | 89.4 (0 refuted) |

(The 256 threaded row's kernel 335 ms / recheck 202 ms is an outlier against fresh 129/111 and eager
116/117 ms on the identical proof term, DAG 60620 in all three: machine noise under slot contention,
not a property of the mode.)

Baseline failure on Branch32+: `symex_one` steps the decided JUMPIs (the `msg.value` condition
rewritten to 0 by `hv`) but stops at the first JUMPI on a call-data word with the goal unsolved, as
on `branchStmt`. The stepper splits it (`step_jumpi_split`), and each child internalizes only its own
`word = 0` / `word ≠ 0`.

**Experiment 1 (persistent parent session with branch-local Grind.Goal vs fresh goals per child,
same statements, same machine).** Threaded: one `mkGoal` at the root (the message, state, substate,
words and `hv`), `Goal.apply` children inherit its `GoalState`, each split child `intros` its path
condition and `internalizeAll` adds only that one declaration. Fresh: every child that needs grind
state gets `mkGoal` + `internalizeAll` of the whole context. Inherited-context internalization cost:
at 256 opcodes 21 declarations / 24.8 ms threaded vs 161 declarations / 50.2 ms fresh (7.7× the
declarations, 2.0× the time; the root's first internalization, ~19-27 ms, dominates the threaded
figure); the fresh count grows with path depth × splits (41, 107, 161) while the threaded one grows
by one per child (11, 17, 21). On these fixtures no premise needed grind (concrete gas), so final
solve time is unchanged; the gap is all in internalization. Proof terms are identical (same DAG).

**Sibling isolation (negative tests, `Verify/Eval/C/Isolation.lean`, log 20261115T051105-C-Isolation,
exit 0).** A 23-byte program whose first JUMPI on `v = msg.value` gives siblings `v = 0` and `v ≠ 0`;
the fall-through computes ISZERO v and jumps to REVERT, the taken side computes ISZERO v and STOPs.
"Every call reverts" is false only on the taken side. `#guard_msgs` pins exactly one open path
(`no rule applies for opcode 0 at pc 16`) in four modes: threaded; threaded + `condRewrite` (ISZERO
results rewritten by `iszero_of_eq` / `iszero_of_ne`, whose side conditions `v = 0` / `v ≠ 0` hold on
one sibling only and are discharged by grind through `Goal.mkSymSimpDischarger` on that sibling's
own internalized state); eager; fresh + `condRewrite`. A leak of the fall-through's `v = 0` into the
taken side would either rewrite its ISZERO to 1 (taking the REVERT jump) or refute its STOP leaf; in
both cases the open path disappears and the guard fails. Positive controls (`msg.value = 0 →`) prove
in threaded, threaded+condRewrite and fresh modes with axioms propext/Classical.choice/Quot.sound.
On a scaling fixture, `BranchNeg64` (5 genuine splits) ends its all-fall-through path in STOP: the
guard pins the one open path at pc 98 in threaded, eager and fresh+eager modes, i.e. none of the
five taken siblings' `word ≠ 0` facts reached the path carrying all five `word = 0`.
Experiment 2 (independent leaf coverage on the frozen exported rows) is lane G's.

A bug found and fixed by these tests: in fresh mode `Grind.mkGoal` (through `preprocessMVar`)
assigns the goal's metavariable to a new one; the discharger and the refutation now work on a copy
or test the returned goal (before the fix, fresh + `condRewrite` failed with "metavariable already
assigned").

## Results on generated VCs (separate from the handwritten rows above)

**c1's dirty-argument theorem (generated by `scripts/refinement/gen.sh` from
`scripts/refinement/corpus/c1.sol`, solar's 83-byte runtime bytecode of `f(uint8)`).** File
`Verify/Eval/C/GenC1.lean`, log 20261115T051109-C-GenC1, exit 0. Statement
`Dirty.TargetDirty code fns` copied verbatim; `target_dirty_base` is the generated proof verbatim
(`dirty_of_frame` + `dirty_symex`); `target_dirty_sym` uses the same reduction and the same
case split on the argument list, then `evm_sym [code eqns] using [hd, hv, loadWord_cdOf_getD,
shr224_cdOf, size_cdOf, size_selectorOf, List.getD_cons_zero]` (the call-data facts as Sym.simp
rewrites whose side conditions Sym.simp discharges itself; `shr224_cdOf` is `shr_cdOf_selectorOf`
restated for the stepper's normal form of SHR).

| proof | result | DAG (tree) | aux DAG | kernel recheck | stepper |
| --- | --- | --- | --- | --- | --- |
| generated (`dirty_symex`) | ok | 7266 (163.7k) | 8239 (45 aux decls) | 22.9 ms | — |
| `evm_sym` | ok, axioms propext/choice/Quot.sound | 7990 (235.2k) | 274 (7) | 19.3 ms | 26 steps, 1 split, 2 decided, the infeasible clean-argument path closed by the E-graph on internalizing its path condition, 101 premises, ~83 ms |

The file-level profile (both proofs together): tactic execution 3.22 s, of which the stepper's
counters account for ~83 ms, so `dirty_symex` is ~3.1 s on this theorem; type checking 160 ms total.

**Certified/verify_counter/Proofs/Runs/Evm*.lean (the generated EVM runs named in the acceptance
note): not piloted.** They are relational segment simulations (`SegRel Agree … (seg (EVM.Program.block
o call sched) …)`) over SolarTV's EVM interpreter, proved by `sym_seg` (evaluation by simp of both
segments), not EthLib `At`/`Hoare` frames; the stepper's fused rules are EthLib frame rules and do
not apply without a parallel rule set for `EVM.Program.block`. Also `verify_counter.gen.Counter.Evm1`
and `.Sched` are not built in this checkout (only `Stage0`), so neither the baseline nor a port could
be checked. The c1 theorem above is the generated end-to-end VC on EthLib frames that is built.

## Owner addenda, status

| item | status |
| --- | --- |
| Carry `Grind.Goal` (one `mkGoal` at the root, `Goal.apply` children, `intros` + `internalizeAll` of each new path condition, fork at JUMPI, facts scoped to descendants; compose branches only through `step_jumpi_split`) | delivered (`Stepper.lean`) |
| Experiment 1: threaded vs fresh, internalization cost and sibling isolation on the EVM fixtures | delivered (Branch32-256, BranchNeg64, Isolation) |
| Sibling-isolation negative test incl. one-sided conditional rewrite side conditions | delivered (`Isolation.lean`, 4 + 3 guarded negatives, 3 positive controls) |
| Measurements on generated VCs | partial: c1 dirty theorem (generated, EthLib) delivered; verify_counter Runs/Evm* not applicable to EthLib frame rules and not built |
| Memory fixtures | not attempted (see above) |

## Adoption proposal

Use precompiled fused backward rules + one `Sym.BackwardRule.apply` per opcode + Sym.simp ground
evaluation with a threaded persistent cache as the EVM frame stepper for EthLib-frame obligations
(dirty-argument proofs, W1-style blocks): per step it does ~0.25 ms of elaboration work against
~56 ms for `evm_step`, and it splits symbolic JUMPIs where `symex_one`'s split alternative fails.
Keep the grind state threaded per branch (`Grind.Goal`): it internalizes 1 declaration per child
instead of the whole context. Before adopting: (1) shrink premise proofs (the stepper's DAGs are
~1.4× larger and its kernel time grows ~×2.7 per doubling; proving the byte/`pc < size` premises by
`decide`-style kernel evaluation instead of Sym.simp proof terms is the next experiment); (2) compile
the stepper (it runs in the interpreter here); (3) add memory rules; (4) keep the guards for runtime
exceptions (`bv_omega` recursion) and reducible-only `assumption`.
