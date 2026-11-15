# Lane G: shared arithmetic facts, grind as a discharger and as an SMT backend, cbv on bounded leaves

Lane G's files are all under Verify/Eval/G/ (Lean modules, generators, run scripts); generated
fixtures and logs live outside the repository under ~/g-gen/ and ~/eval-logs/, reproducible from the
scripts. Every timing below is one run on this shared 5-core machine while other lanes ran (load
average 3-4), with LEAN_NUM_THREADS=1; read ratios, not absolute numbers. Nothing here changes a file
outside the lane, and no claim of speed-up is made without the measurement next to it.

Measurements are marked **[generated]** when the statements are the repository's generated
end-to-end artefacts (exported solver obligations, captured side conditions and leaves of generated
proofs), and **[handwritten]** for the lane's own fixtures.

## 1. The shared-facts discharger (Shared.lean)

- g_simp [rw...] using [trig...]: Sym.simp rewrites with conditional lemmas; every side condition is
  proved by grind from ONE fact state: the goal's local context (path conditions, word facts) is
  internalized once (Grind.mkGoal on a fresh goal False in that context, Goal.internalizeAll), the
  trigger lemmas are the only E-matching theorems (Grind.mkOnlyParams: no @[grind] set), and
  Goal.mkSymSimpDischarger runs each side condition on a copy of that state (its own solver state is
  dropped). g_facts [eq...] instantiates equations once at every matching subterm of the goal and
  hypotheses (eager facts instead of triggers).
- Branch discipline: g_split_simp c splits with MVarId.byCases; each child extends a persistent copy
  of the parent's state by its own hypothesis only (factsAt with a parent). Nothing outlives one
  GrindM.run, so no cache survives the branch.
- Inconsistent contexts (a finding about the pinned Lean): when the shared context is already
  contradictory, grind closes the goal it holds during internalizeAll and marks the state
  inconsistent; every later Goal.dischargeSymSimp then returns .solved with its proof metavariable
  UNASSIGNED (solve sees the inherited flag and assigns nothing). It fails closed (the elaborator
  rejects a declaration with metavariables; seen on a real abi_hash path), but an adopter must
  record the proof of False itself: Facts keeps it (the fact goal has type False, so grind assigns
  it) and the discharger answers False.elim of it.
- Sibling-isolation negatives (Tests.lean, run under check.sh): sibling_isolation splits on x = 0;
  each child has one conditional rewrite whose side condition only its own hypothesis proves (the
  read through the store at x moves only when x = 0, the one through the store at y only when
  x ≠ 0), and each child is closed by exact with a hypothesis stating exactly the form it must have.
  A fact or a cached discharge crossing siblings changes that form, and the exact fails; the
  contradictory pair x = 0 / x ≠ 0 also means a leaked E-graph would discharge everything.
  sibling_isolation_shared_cache keeps ONE Sym.simp cache across both children (positive first):
  grind discharges are context dependent, and the test passes. sibling_isolation_rejects_leak runs a
  deliberately wrong control (negative child discharged from the positive child's state) inside
  fail_if_success: it leaks (its negative child is rewritten, checked by hand in a probe) and the
  same test rejects it. All proofs: propext, Classical.choice, Quot.sound.

## 2. Scaling family [handwritten] (gen_scaling.py, run_scaling.sh)

A read at q through N stores at p + 32 i on a path with p < 2^64, p + 32 N <= q, q < 2^64 and 16 unrelated
path conditions; each Mem.read_store_disjoint rewrite raises the side condition of SolarTV's lemma
of that name over the same hypotheses (Model.lean copies the shapes in pure Lean). Elaboration time
including the kernel check (ms) / kernel time of the proof and all its auxiliary declarations (ms):

| N | base (W1Proofs sym_mem_disch_core per side condition) | once (normalize once, omega each) | fresh (grind only per side condition) | shared (g_simp) | facts (g_facts + g_simp) |
|---|---|---|---|---|---|
| 16 | 696 / 354 | 472 / 317 | 1633 / 206 | 1172 / 213 | 1210 / 195 |
| 32 | 1451 / 751 | 956 / 715 | 3398 / 444 | 2212 / 355 | 3040 / 384 |
| 64 | 3104 / 1596 | 1897 / 1393 | 7201 / 951 | 4364 / 719 | 10524 / 755 |
| 128 | 5794 / 2823 | 3723 / 2943 | 14115 / 2541 | 9561 / 1689 | 59598 / 2570 |
| 256 | 11635 / 5921 | 8074 / 7081 | 27966 / 5408 | 19609 / 3577 | 710640 / 3899 |

Proof size at 256 (DAG of the theorem + DAG of its auxiliary declarations): base 46,471 + 464,603;
fresh 7,308 + 348,097; shared 105,709 + 0. Peak RSS at 256: base 1.86 GB, shared 2.08 GB.
All axioms: base and once propext, Quot.sound; the grind variants add Classical.choice.

Reading: sharing the internalized context makes grind 30% cheaper than grind per side condition
(fresh) and its kernel check 40% cheaper than omega's, but grind's per-attempt solve still costs
more than omega here: shared is 1.7x base's elaboration time and 2.4x "once" (normalize the
hypotheses once, then omega). Preloading all the arithmetic (facts) is superlinear (12 minutes at
256): every attempt re-solves over every preloaded constraint. The cheapest change to today's
discharger is "once": hoist sym_mem_disch_core's simp ... at * normalization out of the per-rewrite
discharger.

## 3. Real side conditions of generated stage proofs [generated] (capture.sh, gen_real.py, Bench.lean)

Capture/Hook.lean is a second elaborator for W1Proofs' sym_mem_disch: it prints each side condition
with its whole context as a standalone theorem and runs the original. Captured from the unchanged
stage proofs of Certified/{abi_hash,masks,events}/Proofs/Runs/*.lean (their generated stages compiled
outside .lake):

| contract | sym_mem_disch calls | proved | failed | time in the discharger | of which on failures |
|---|---|---|---|---|---|
| abi_hash | 293 | 59 | 234 | 2.84 s | 2.58 s |
| masks | 659 | 39 | 620 | 10.89 s | 10.57 s |
| events | 226 | 26 | 200 | 3.64 s | 3.55 s |

About 90% of the calls are speculative rewrites that fail, and they take about 95% of the time: the
discharger's cost is its failures, each paying simp ... at * over the whole path context. Most
targets are closed (literal offsets); the others are BitVec.toNat of an unevaluated match = 0.
Real/<C>.lean restates them verbatim, one theorem per path context with the candidates in the order
asked, and g_compare runs three dischargers on each (base = the repository's own sym_mem_disch;
shared = one grind fact state per context; ground = decide on closed candidates, the rest to the
shared state), timing every attempt and kernel-checking every proof found, and warns on every
candidate where a variant and the base disagree:

| contract (check.sh run) | candidates | proved (all three agree) | base: sym_mem_disch each | shared grind state | ground first, then shared | kernel of found proofs (base / shared / ground) |
|---|---|---|---|---|---|---|
| AbiHash (exit 0, 15 contexts, 0 disagreements, 0 errors) | 293 | 59 / 59 / 59 | 3832 ms | 2110 ms | 1465 ms | 28.1 / 17.0 / 9.7 ms |
| Masks (exit 0, 29 contexts, 6 disagreements, 0 errors) | 659 | 39 / 36 / 36 | 27017 ms | 19957 ms | 17720 ms | 45.1 / 34.0 / 16.2 ms |
| Events (exit 0, 15 contexts, 0 disagreements, 0 errors) | 226 | 26 / 26 / 26 | 2257 ms | 1532 ms | 1483 ms | 5.7 / 7.1 / 3.4 ms |

- abi_hash and events: all three prove exactly the same candidates; shared takes 0.55-0.68x the
  base's time and ground-first 0.38-0.66x, because the failing attempts no longer pay the
  per-call simp ... at * over the path context.
- masks: grind misses 3 of base's 39 (two BitVec.toNat (match ...) = 0 and one 100 = 0, all true only
  because the path context is contradictory, which omega finds after bitvec_to_nat normalization and
  grind does not), so the shared discharger is not a drop-in replacement there. Elaboration times on
  masks moved between two runs (base 14.1 s, then 27.0 s under load); the ratios held (0.74-0.99 for
  shared, 0.63-0.80 for ground-first).
- A first version of ground-first sent a closed candidate that decide refutes nowhere else; on masks
  it then missed candidates that hold only from a contradictory context. Fixed (they go to the
  shared state); the table is the fixed version.

## 4. Leaves of bump's generated loop proof [generated] (Capture/BumpLeaves.lean, gen_leaves.py)

Contracts/VerifyCounter/Bump.lean (invariant generated into Inferred.lean) closes its segment
leaves with total_leaf (bv_omega / sym_omega). Capture/BumpLeaves.lean reruns tseg0/tseg7/tseg10
verbatim and BumpWrongRank's growing-rank back edge, capturing 15 leaves (14 closed, 1 the wrong
rank's, which fails). Real/BumpLeaves.lean restates each verbatim, proved by total_leaf (old), by
total_leaf with grind [EvmRules.Evm.add] in place of bv_omega/sym_omega (grind), and with a leaf's
arithmetic subgoals closed from one shared fact state (shared, g_close_all):

- coverage: old 14/14, grind 9/14, shared 9/14; the wrong-rank leaf fails for all three
  (fail_if_success), as BumpWrongRank requires. The 5 leaves grind and shared do not close are
  emitted as fail_if_success checks (gen_leaves.py's EXPECT_FAIL list), so the file carries no sorry
  (check.sh exit 0; axioms propext, Quot.sound or propext, Classical.choice, Quot.sound) and the gap
  stays executable: if grind starts closing one of them, its check fails.
- 6 of the 9 are closed by total_leaf's first, non-arithmetic alternatives (identical in all
  variants). On the 3 leaves where the arithmetic closer runs (leaf0/4/6): old 213 ms / kernel
  100.6 ms, grind 231 ms / 27.5 ms, shared 226 ms / 25.4 ms: same elaboration, a 4x smaller kernel
  check.
- grind fails on the 5 hardest leaves (old needs 98-942 ms there): loop-exit Post leaves with the
  storage update, where grind takes BitVec extensionality instead of the toNat arithmetic; -ext and
  adding Evm.add as the one extra lemma did not change that.
- axioms: old propext, Quot.sound (Classical.choice on two leaves); grind propext, Classical.choice, Quot.sound.

## 5. grind as an SMT backend on the frozen solver obligations [generated] (VcGrind.lean, discharge_g.sh)

vc_grind = vc_valid_prep; intros; vc_grind_norm (vc_smt_norm copied verbatim, so no SMT plugin is
imported); grind. discharge_g.sh is a lane copy of discharge.sh that runs EVERY backend on EVERY row,
keeps the statement 'theorem obligation : <ob>.Valid', the input lock, the semantics hashes, the
construct grep and the per-row axiom gate, and records wall time, peak RSS, elaboration+kernel,
kernel (with auxiliaries) and proof DAG per probe. Vacuity by grind: yes or unknown, never no.

Inputs: the frozen exports in the checkout are Contracts/Vault/Vc and Contracts/ArrayMax/Vc (solar
7f4e94e, line 2 read back as 'import SolarVerify'): every module hashes as Verify/Discharge/frozen/<C>.sha256
and frozen/v2/<C>.sha256 list. Counter's and Token's exports are not in the checkout (their locks are),
so their 27 rows are not run.


Vault: 17 required rows measured.

| backend | proved | median elab+kernel (ms) | median kernel (ms) | median proof DAG | max RSS (MB) | axioms of proved rows |
|---|---|---|---|---|---|---|
| vc_valid | 14/17 proved | 1596 | 245 | 24152 | 1659 | propext Classical.choice Quot.sound |
| vc_grind | 17/17 proved | 1643 | 254 | 40112 | 1659 | propext Classical.choice Quot.sound |
| vc_grind_nl | 17/17 proved | 1611 | 244 | 40112 | 1655 | propext Classical.choice Quot.sound |
| cert | 0/17 proved | - | - | - | - | none built |
| vacuity(vc_grind) | 5/17 yes (vacuous) | 1719 | 237 | 42667 | 1659 | propext Classical.choice Quot.sound |
- Vault.deposit#7 vc_valid: failed: ~/g-gen/discharge/Vault/probe/Vault_deposit_7_row_vc_valid.lean:8:65: error: Tactic `simp` failed with a nested error: maximum recurs
- Vault.withdraw#6 vc_valid: failed: ~/g-gen/discharge/Vault/probe/Vault_withdraw_6_row_vc_valid.lean:8:66: error: omega could not prove the goal: a possible counterexamp
- Vault.withdraw#8 vc_valid: failed: ~/g-gen/discharge/Vault/probe/Vault_withdraw_8_row_vc_valid.lean:8:66: error: Tactic `simp` failed with a nested error: maximum recur
- vacuous by grind: Vault.deposit#6, Vault.deposit#7, Vault.withdraw#6, Vault.withdraw#7, Vault.withdraw#8

ArrayMax: 19 required rows measured.

| backend | proved | median elab+kernel (ms) | median kernel (ms) | median proof DAG | max RSS (MB) | axioms of proved rows |
|---|---|---|---|---|---|---|
| vc_valid | 16/19 proved | 1911 | 167 | 22319 | 3118 | propext Classical.choice Quot.sound |
| vc_grind | 16/19 proved | 1243 | 155 | 22046 | 1649 | propext Classical.choice Quot.sound |
| vc_grind_nl | 3/3 proved | 1059 | 129 | 17697 | 1619 | propext Classical.choice Quot.sound |
| cert | 0/19 proved | - | - | - | - | none built |
| vacuity(vc_grind) | 0/19 yes (vacuous) | - | - | - | - | - |
- ArrayMax.max#8 vc_valid: failed: timeout
- ArrayMax.max#8 vc_grind: failed: ~/g-gen/discharge/ArrayMax-b/probe/ArrayMax_max_8_row_vc_grind.lean:8:64: error: `grind` failed case grind.1.1.1.1.1.1.1.1.1 
- ArrayMax.max#9 vc_valid: failed: timeout
- ArrayMax.max#9 vc_grind: failed: ~/g-gen/discharge/ArrayMax-b/probe/ArrayMax_max_9_row_vc_grind.lean:8:64: error: `grind` failed case grind.1.1.1.1.1.1.1.1.1.1.1.1.1 
- ArrayMax.max#10 vc_valid: failed: timeout
- ArrayMax.max#10 vc_grind: failed: ~/g-gen/discharge/ArrayMax-b/probe/ArrayMax_max_10_row_vc_grind.lean:8:65: error: `grind` failed case grind.1.1.1.1.1.1.1.1.1.1 
- vacuous by grind: none
- negative (Vault, goal negated as test/smt-negatives.sh N4): vc_valid failed: ~/g-gen/discharge-neg/Vault/probe/Vault_withdraw_0_ro; vc_grind failed: ~/g-gen/discharge-neg/Vault/probe/Vault_withdraw_0_ro
- negative (ArrayMax, goal negated as test/smt-negatives.sh N4): vc_valid failed: timeout; vc_grind failed: ~/g-gen/discharge-neg/ArrayMax/probe/ArrayMax_max_8_r

- Vault: vc_grind 17/17, vc_valid 14/17 (deposit#7 and withdraw#8 hit maxRecDepth inside its simp,
  withdraw#6 omega fails); grind finds exactly README's five vacuous rows. ArrayMax: both 16/19, the same
  three rows (max#8, #9, #10) fail for both (vc_valid by the 60 s timeout; the repository proves them
  with vc_bounded_valid). Proof cost is dominated by vc_valid_prep, shared by every backend: medians
  1.2-1.9 s and 150-250 ms of kernel per row for both solvers.
- Negatives (N4 of test/smt-negatives.sh, goal negated in the locked module copy): every backend fails
  on Vault.withdraw#0 and ArrayMax.max#8; vc_grind fails fast, vc_valid on the negated max#8 by its 60 s
  timeout, which smt-negatives would count against a backend.

Experiment (2) of the clarification, grind's independent leaf coverage on the locked rows, is the
table above: each row its own Lean process and theorem, nothing shared across rows. Experiment (1)
(persistent parent session vs fresh child goals) is lanes B and C's; Shared.lean's g_split_simp and
Tests.lean are the branch-local Grind.Goal pieces with their sibling-isolation negatives.

lean-smt (vc_smt): not run here. Verify/Discharge/Reconstruct is a separate package (lean-smt 6b26285,
lean-cvc5 d19a134 with a downloaded cvc5, lean-auto); its .lake is absent, the GitHub remotes answer
through the proxy, but building it is a new build the owner ruled out for lanes. Its recorded proofs
(Verify/Discharge/results/v2/*/results.tsv) rest on propext, Classical.choice, Quot.sound, 63/63.

## 6. cbv on bounded leaves [generated / repository leaves] (Cbv/Sat.lean, Cbv/Mulx.lean)

Identical statements, four ways: decide, decide +kernel, decide_cbv, cbv.


| statement | variant | elab+kernel (ms) | kernel (ms) | proof DAG (+aux) | axioms |
|---|---|---|---|---|---|
| s1 | decide | 5.3 | 0.93 | 76 (+0) | propext |
| s1 | kernel | 2.8 | 0.98 | 1 (+76) | propext |
| s1 | dcbv | 43.5 | 4.46 | 2397 (+0) | propext |
| s1 | cbv | 12.4 | 4.72 | 2364 (+0) | propext |
| s2 | decide | 5.1 | 0.96 | 79 (+0) | propext |
| s2 | kernel | 2.9 | 0.97 | 1 (+79) | propext |
| s2 | dcbv | 10.4 | 4.41 | 2368 (+0) | propext |
| s2 | cbv | 11.7 | 4.68 | 2335 (+0) | propext |
| s3 | decide | 6.8 | 0.83 | 79 (+0) | propext |
| s3 | kernel | 2.8 | 0.87 | 1 (+79) | propext |
| s3 | dcbv | 7.6 | 2.83 | 1541 (+0) | propext |
| s3 | cbv | 8.5 | 2.82 | 1507 (+0) | propext |
| s4 | decide | 5.6 | 1.04 | 83 (+0) | propext |
| s4 | kernel | 3.2 | 1.15 | 1 (+83) | propext |
| s4 | dcbv | 13.7 | 5.38 | 3109 (+0) | propext |
| s4 | cbv | 14.5 | 5.54 | 3072 (+0) | propext |
| g1 | vc_ground | 4.2 | 0.22 | 69 (+0) | propext, Quot.sound |
| g1 | decide | 2.1 | 0.20 | 78 (+0) | propext, Quot.sound |
| g1 | kernel | 1.9 | 0.26 | 52 (+70) | propext, Quot.sound |
| g1 | dcbv | 2.4 | 0.32 | 139 (+0) | propext, Quot.sound |
| g2 | vc_ground | 3.4 | 0.35 | 116 (+0) | propext, Quot.sound |
| g2 | decide | 3.7 | 0.45 | 125 (+0) | propext, Quot.sound |
| g2 | kernel | 3.0 | 0.42 | 93 (+117) | propext, Quot.sound |
| g2 | dcbv | 4.4 | 0.58 | 238 (+0) | propext, Quot.sound |
| (check-Cbv_Sat.out) | check.sh | exit 0, wall 0:02.47, peak 1560 MB | | | |
| items_eq | decide | 101.2 | 41.84 | 49 (+0) | propext, Quot.sound |
| items_eq | kernel | 45.1 | 43.41 | 1 (+49) | propext, Quot.sound |
| items_eq | dcbv | 2877.5 | 114.17 | 47027 (+10) | propext, Quot.sound |
| items_eq | cbv | 264.8 | 105.69 | 47011 (+10) | propext, Quot.sound |
| walk_eq | decide | 1356.7 | 857.54 | 75 (+0) | propext, Quot.sound |
| walk_eq | kernel | 933.3 | 880.81 | 1 (+75) | propext, Quot.sound |
| walk_eq | dcbv | 14328.0 | 13080.39 | 227093 (+10) | propext, Quot.sound |
| walk_eq | cbv | 14171.7 | 11660.01 | 227069 (+10) | propext, Quot.sound |
| (check-Cbv_Mulx.out) | check.sh | exit 0, wall 1:15.77, peak 2331 MB | | | |

cbv's proofs are explicit Sym.Simp rewrite chains: 30-160x larger and 2-18x slower to check than
the kernel's own evaluation on these leaves; on mulx's walk_eq (the bytecode walk) cbv takes 17 s
and a 227k-node proof where decide +kernel takes 1 s. The negatives (a step that does not check,
a hint naming no clause, no empty clause, a true closed hypothesis for vc_ground, a flipped
bytecode byte) fail for every variant. No change proposed to Assembly.lean or its generator.

## 7. Measurement pitfall found

Common/Measure.lean's #kernel_recheck takes env.toKernelEnv inside its timed region. With
asynchronous elaboration that call waits for earlier theorems' pending kernel checks: a 0.2 ms proof
was reported as 2.5 s. Kernel.lean (#kernel_recheck_all) and Bench.lean take it outside the timer
(lanes A and H told). The scaling family (one theorem per file, Elab.async false) is unaffected,
checked at N = 16.

## Status of the addendum items

- vc_grind backend with vc_smt's prep/normalization, plugin-free: delivered (VcGrind.lean).
- runner that runs all backends on every row with separate metrics: delivered (discharge_g.sh), on
  Vault and ArrayMax (36 of 63 rows); Counter and Token not attempted (exports absent).
- cert backend: not run, Contracts/<C>/Proofs modules are in no lake library and not built.
- vc_smt: not attempted (Reconstruct package not built; no new builds).
- order LIA/EUF, arrays, nonlinear, bitvectors: Vault (LIA/EUF + arrays) and ArrayMax (quantified
  arrays) done; nonlinear and bitvector rows are not in the available exports.
- negatives: N4 goal negations of Vault.withdraw#0 and ArrayMax.max#8 rerun for vc_valid and vc_grind (below).
- cbv pilot: delivered on Sat leaves, vc_ground leaves and mulx items_eq/walk_eq.
- generated end-to-end VCs (owner's acceptance): Bump leaves, captured stage side conditions and the
  frozen rows above.

## Files that need generated stages outside .lake

Capture/AbiHash.lean and Cbv/Mulx.lean import abi_hash.gen.* and mulx.gen.*, which no lake library
builds; capture.sh compiles them into ~/g-build (outside .lake) and the runs pass LEAN_PATH=~/g-build.
A library build or an audit without that path cannot elaborate these two files: exclude them, or
build those gen modules first.
