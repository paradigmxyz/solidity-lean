# Lane E: proof shape (DAG, kernel time, .olean) — results

Files: Verify/Eval/E/ (Toy.lean, Stats.lean, gen.py, gen_evm.py, run.sh, parse.py, setup.sh,
report.py, generated.sh, Fixtures/ = the N=16 instance of every variant, results.jsonl = every
measured run, generated.log = the generated-module run).

Reproduce: Verify/Eval/E/setup.sh; python3 Verify/Eval/E/gen.py DIR; python3
Verify/Eval/E/gen_evm.py DIR; E_NOSLOT=1 Verify/Eval/E/run.sh DIR/<fixture>.lean (one at a time);
python3 Verify/Eval/E/report.py; E_NOSLOT=1 Verify/Eval/E/generated.sh.

## What was measured, and how

Two kinds of measurements, kept apart:

* **A. Handwritten / synthetic fixtures** (sections 1–4). Every variant of one family and size proves
  the same theorem main (same statement text); only the proof's shape differs.
  * EvmJoin / EvmChain: real EthLib evm_step / evm_stop on NatCode programs (code as one Nat,
    NatCode.ofNat, as W1.lean), Spec/Hoare/At/Triple.seq from EthLib Logic.
  * Join / Chain: the same programs on an EVM-shaped pure-Lean toy machine (Toy.lean: NatCode-style
    bytes, walk-validated jump destinations, symbolic gas g - c closed by omega), with the generator
    emitting each rule application explicitly.
  * SolM: Verify/Basic.lean's SolM with Loom wp; one sub-program S of L storage updates in both
    branches of prog c := if c then (sstore 0 1; S) else (sstore 0 2; S).
* **B. Generated end-to-end artefacts already in the checkout** (section 5): every theorem of the
  built generated modules rechecked by #e_module_stats. No lake build was run.

Programs. join: dispatcher of P=4 paths (DUP1 PUSH1 i EQ PUSH1 A_i JUMPI), a path-private block
A_i, then PUSH1 B JUMP into one shared block B (JUMPDEST, body, STOP); unique opcodes for
N=16/32/64/128/256 are 50/56/98/152/290 (the dispatcher is a fixed ~17). chain: N opcodes of
PUSH1 k ADD SWAP1 (symbolic words grow along the run), cut into N/8 blocks of 8.

Variants. join: inline (each path re-steps B; jump-destination facts re-proved inline), helper (as
inline but B's destination fact is one theorem, experiment 1), shared (B is one lemma general in
its two stack words and its gas, experiment 2), perblock (every A_i and B is a lemma). chain:
mono (one proof stepping all N opcodes = what evm_step emits today), linLit/balLit (per-block
Hoare lemmas on literal frames, composed by a right-nested Spec.seq chain / a balanced Triple.seq
tree), linDef/balDef (same with every frame behind a def F_i), experiment 3.

Metrics. kernel ms (recheck all) = #kernel_recheck of every theorem of the fixture summed
(#e_stats, single-threaded, the primary kernel number); kernel ms (prof) = profiler type checking;
max decl kernel = the slowest single declaration; DAG = Expr DAG nodes after ShareCommon (sum over
decls, and union = all decls shared together); tree = tree nodes (capped 1e7 per decl); decls
includes aux decls (_proof_ from omega, decide +kernel aux lemmas); .olean bytes of lean -o;
peak RSS from /usr/bin/time; wall ms; elab ms (wall-based) = wall - import - interpreted stats
commands - kernel (the profiler's elaboration sums overlap because theorem bodies elaborate as
tasks, so the profiler sum is reported but not used for ratios). x2 = ratio to the previous size.
Runs were sequential (LEAN_NUM_THREADS=1, -M 5000) but the machine was shared with other lanes:
single ratios carry ~±30% noise; trends over 4 doublings are what is reported.

Checks. #print axioms of every 128 variant main and of the generated stage0_post:
[propext, Quot.sound] (toy) / [propext, Classical.choice, Quot.sound] (EVM, Bump) — no sorryAx.
#kernel_reject_check passes. Negatives: EvmChain16 mono and balDef with start gas 10 instead of
10000000 are rejected (evm_step finds no rule / block lemma type mismatch); toy Join16 shared with
blockB's gas hypothesis weakened to 2 is rejected (omega). The inline EVM join's aux decls were
inspected: decide +kernel's walk proofs are emitted as _proof_ aux theorems and the identical
B-destination fact appears once (deduplicated by type), not once per path.

## 1. Shared helper declarations (repeated sub-fact)

Toy Join, kernel recheck-all ms (inline → helper): 937→781, 893→904, 2327→2179, 3858→3415,
7480→7600 at N=16..256; DAG union identical (84127 vs 84128 at 16; 1.10M both at 256); .olean
identical. **No effect.** A repeated closed fact (the B destination's validity) is a syntactically
identical term, so the kernel's infer/whnf caches inside a declaration and ShareCommon in the
.olean already share it; on the EVM side Lean's decide +kernel already abstracts it into one aux
theorem per distinct statement. A helper only pays when the repeated fact is not syntactically the
same at each use (different frames) — i.e. when it is a stated, generalized lemma, which is
experiment 2.

## 2. Shared block continuations (paths joining at a block)

EvmJoin (real evm_step), kernel recheck-all ms / max single decl ms / wall s / .olean MB:

| N (unique ops) | inline | shared (B lemma) | perblock (A_i + B lemmas) |
|---|---|---|---|
| 64 (98) | 324 / 50 / 12.2 / 1.10 | 214 / 29 / 7.5 / 0.89 | 296 / 14 / 6.2 / 0.94 |
| 128 (152) | 1132 / 216 / 22.0 / 1.75 | 341 / 41 / 9.6 / 1.35 | 453 / 30 / 9.2 / 1.40 |
| 256 (290) | 1229 / 270 / 48.9 / 3.32 | 781 / 70 / 24.3 / 2.48 | 1200 / 51 / 21.2 / 2.54 |

Toy Join at 256: inline 7480 ms kernel, DAG sum 1.10M, .olean 23.8 MB; shared 3778 ms, 0.54M,
10.3 MB; perblock 3976 ms, 0.62M, 7.3 MB.

* Sharing B halves kernel and wall time and cuts .olean by ~25% (EVM) to ~57% (toy) at P=4
  paths; the saving is (P-1)·|B|, so it grows with the number of paths reaching a block.
* inline's slowest single declaration grows superlinearly (EVM 50→216→270 ms; x2 4.3 at 64→128
  for 1.55x more unique opcodes), while shared/perblock keep every declaration small
  (≤70 ms at 256).
* Kernel time of shared scales ~linearly in UNIQUE opcodes: 214→341→781 ms for 98→152→290
  unique (ratios 1.6/2.3 for size ratios 1.55/1.9).
* perblock (a lemma for path-private blocks too) does not lower total kernel time vs shared
  (no reuse to gain) and adds ~20% decl overhead, but gives the smallest per-declaration cost and
  the lowest wall time (theorem bodies elaborate in parallel and fail independently).

## 3. Composition: balanced vs linear, frames behind defs vs literal

EvmChain (real evm_step), kernel recheck-all ms / max decl ms / wall s / elab (wall-based) s:

| N | mono | linLit | balLit | linDef | balDef |
|---|---|---|---|---|---|
| 64 | 107 / 24 / 4.0 / 2.3 | 133 / 11 / 2.5 / 0.7 | 116 / 6 / 2.9 / 0.8 | 117 / 6 / 2.7 / – | 116 / 6 / 2.8 / 0.7 |
| 128 | 439 / 125 / 10.0 / 6.1 | 230 / 10 / 4.5 / 0.9 | 217 / 7 / 4.9 / 0.9 | 216 / 6 / 5.5 / 1.2 | 330 / 25 / 5.3 / 0.9 |
| 256 | 335 / 100 / 16.2 / 11.5 | 562 / 19 / 10.4 / 1.9 | 566 / 13 / 10.7 / 2.5 | 507 / 8 / 9.4 / 2.2 | 500 / 13 / 10.0 / 2.4 |

.olean at 256: mono 1.87 MB, Lit 1.95 MB, Def 1.99 MB. Toy Chain: all five variants within noise
of each other at every size (kernel x2 ≈ 2.0–2.5, DAG x2 = 2.00; 256: 3.4–4.2 s), because there
the per-step omega proofs dominate.

* **Splitting into per-block declarations is what matters.** mono (one evm_step proof) has the
  worst single declaration (100–125 ms vs ≤25) and its elaboration grows superlinearly
  (6.1 s at 128, 11.5 s at 256, vs 0.9–2.5 s for any block-split variant: the one long tactic
  proof carries an ever larger goal and metavariable context). Total kernel time is similar
  (all ~linear: DAG x2 ≈ 1.95).
* **Balanced vs right-nested linear composition: no measurable difference** up to k = 32 blocks.
  A Triple.seq node is O(1) to check given its three frames, so the chain is O(k) either way; the
  kernel never re-traverses the nested proof. Depth would only matter for recursion limits far
  beyond these sizes.
* **Frames behind defs vs literal: no measurable kernel difference** here (and defs add one decl
  per frame, +2% .olean). Literal frames are shared subterms (DAG), not re-checked trees: the
  chain's frames have tree/DAG ratios of ~35 but the kernel and .olean see the DAG. Defs help the
  elaborator/pretty printer and keep statements short; they are not needed for kernel cost.

## 4. Source level (SolM, Loom wp)

| L | inline kernel ms / wall s / .olean MB | shared (S lemma + wp_cons) |
|---|---|---|
| 16 | 76–147 / 7.9 / 2.25 | 64–83 / 4.6 / 1.65 |
| 32 | 1029–1151 / 54.1 / 20.3 | 950–1051 / 25.3 / 16.6 |
| 64, 128, 256 | simp timeout at maxHeartbeats 1e6 | simp timeout at maxHeartbeats 1e6 |

Sharing S halves elaboration (two simp runs of S become one) but kernel time and .olean barely
move, and both variants are ~x13 per doubling of L: the cost is inside S itself — after k
sstores, Basic.lean's storage is a k-deep fun k => if … closure and every later sload/simp step
walks it (quadratic VC, huge proof terms: 600k DAG nodes and 20 MB .olean at L=32). At source
level the shape fix is a storage VC that does not grow (frame/footprint lemmas per slot, or one
lemma per straight-line segment whose postcondition names only the slots it writes), not proof
sharing.

## 5. Generated end-to-end artefacts (not handwritten)

Verify/Eval/E/generated.sh, #e_module_stats over every theorem of each built generated module
(one slot, nothing built). Log: Verify/Eval/E/generated.log.

| module | .olean B | theorems (aux) | kernel recheck ms | DAG sum | tree sum | slowest |
|---|---|---|---|---|---|---|
| Contracts.VerifyCounter.Bump | 4,405,160 | 97 (75) | 1149 | 102,827 | 54.7M | tseg0 218 ms (dag 18,490, tree 5.85M), tseg10 181, tseg7 168 |
| Contracts.VerifyCounter.BumpTotal | 3,417,352 | 83 (76) | 1234 | 100,545 | 54.7M | wseg0 249 ms (dag 18,499, tree 5.85M), wseg10 174, wseg7 132 |
| W1Proofs.Segment | 1,139,832 | 10 (1) | 8 | 2,303 | 24k | – |
| Contracts.VerifyCounter.Inferred | 59,536 | 0 | – | – | – | (defs only) |
| verify_counter.gen.Counter.Stage0 | 579,936 | 0 | – | – | – | (defs only) |

Peak RSS 1.65 GB, 27 s wall for the whole run. Not built, so not measured (needs_from_lead):
BumpWrongRank, Certified/verify_counter/Proofs/{Stages,Execution,Assembly,Runs/*},
verify_counter.gen.Counter.Evm*, Contracts.Counter.VC.Export, Verify.VC.*.

Reading: the generated Bump proof already has the recommended shape — one theorem per cut-point
segment (tseg0/7/10), composed once by CutPoint.ends_of_start — so its kernel cost is linear in
segments and its three segment theorems are ~50% of the module's kernel time. Inside a segment
the terms are extremely shared (tree/DAG ≈ 300; 75 of 97 theorems are abstracted _proof_ leaves),
the same effect as section 1: repeated sub-terms cost the kernel and .olean once.

## Conclusions — how a generator should emit proofs

1. **One declaration per basic block (cut point), stated generally** — universally quantified
   over the stack words and gas (or the frame fields) that differ between incoming paths, with
   the gas/frame side condition as a hypothesis — and every path that reaches the block closes
   with that lemma. This is the only shape change with a large measured effect: kernel and wall
   ~2x at P=4 joining paths, .olean −25…−57%, per-declaration kernel cost bounded, and total kernel
   time near-linear in unique program size; inline re-stepping is O(paths × block) and its single
   declaration grows superlinearly.
2. **Do not run one long evm_step proof over a whole function**: cut at block boundaries even when
   nothing is shared (EvmChain mono: elaboration 11.5 s vs ~2 s at 256 opcodes, slowest decl 5–10x).
3. **Composition order and frame naming are free choices**: right-nested Spec.seq chains are as
   cheap as balanced trees up to 32 blocks, and literal frames cost the same as defs; emit whichever
   is simplest (a linear chain, literal frames; defs only for readability).
4. **Do not bother hoisting identical closed facts** (jump destinations, code bytes, constant gas
   bounds): the kernel cache, ShareCommon and decide +kernel's aux-lemma dedup already share them.
   Hoist only facts that differ syntactically per use but are instances of one general statement.
5. At source level (Loom/SolM), sharing a sub-program halves elaboration but the dominant cost is
   the growing storage closure; that needs frame lemmas per segment, not proof sharing.

## Appendix: full tables (Verify/Eval/E/report.py on results.jsonl)

### Chain

| variant | N | wall ms | elab ms (wall-based) | elab ms (profiler sum) | kernel ms (prof) | kernel ms (recheck all) | max decl kernel ms | DAG (all decls, shared) | DAG sum | tree sum | decls | .olean B | RSS KB | x2 kernel | x2 elab | x2 DAG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| balDef | 16 | 1600 | 139 | 220.2 | 226.0 | 169.67 | 8.1 | 22244 | 33485 | 1538675 | 35 | 752224 | 1607988 | - | - | - |
| balDef | 32 | 2530 | 180 | 399.5 | 484.0 | 351.78 | 9.85 | 45053 | 68458 | 3181575 | 69 | 1503016 | 1625020 | 2.07 | 1.29 | 2.03 |
| balDef | 64 | 4740 | 512 | 1533.2 | 871.0 | 732.6 | 11.86 | 90755 | 138744 | 6511249 | 137 | 3007352 | 1649888 | 2.08 | 2.84 | 2.01 |
| balDef | 128 | 10510 | 1113 | 2725.9 | 1780.0 | 1829.05 | 33.65 | 182071 | 280264 | 13344323 | 273 | 6013088 | 1708424 | 2.50 | 2.17 | 2.01 |
| balDef | 256 | 21560 | 3225 | 7161.6 | 3520.0 | 3544.59 | 33.23 | 364779 | 567476 | 27707145 | 545 | 12027256 | 1845932 | 1.94 | 2.90 | 2.00 |
| balLit | 16 | 1660 | 118 | 177.2 | 212.0 | 174.46 | 9.13 | 22202 | 33438 | 1539023 | 35 | 748000 | 1608172 | - | - | - |
| balLit | 32 | 2730 | 185 | 604.1 | 501.0 | 363.67 | 11.09 | 44986 | 68399 | 3183207 | 69 | 1495928 | 1624080 | 2.08 | 1.57 | 2.03 |
| balLit | 64 | 5010 | 400 | 1752.7 | 1050.0 | 812.24 | 14.42 | 90638 | 138651 | 6518217 | 137 | 2994472 | 1653616 | 2.23 | 2.16 | 2.01 |
| balLit | 128 | 9570 | 822 | 3931.6 | 2460.0 | 1577.12 | 11.63 | 181854 | 280105 | 13372019 | 273 | 5988688 | 1719712 | 1.94 | 2.06 | 2.01 |
| balLit | 256 | 22100 | 2380 | 9059.1 | 4460.0 | 3924.33 | 36.3 | 364362 | 567187 | 27817621 | 545 | 11979752 | 1863688 | 2.49 | 2.90 | 2.00 |
| linDef | 16 | 1760 | 135 | 203.0 | 230.0 | 172.65 | 7.36 | 22244 | 33480 | 1538669 | 35 | 752224 | 1608236 | - | - | - |
| linDef | 32 | 3290 | 325 | 895.9 | 595.0 | 478.68 | 32.5 | 45054 | 68454 | 3181557 | 69 | 1503048 | 1623336 | 2.77 | 2.41 | 2.03 |
| linDef | 64 | 4600 | 481 | 1681.4 | 902.0 | 704.82 | 10.89 | 90758 | 138742 | 6511207 | 137 | 3007448 | 1650556 | 1.47 | 1.48 | 2.01 |
| linDef | 128 | 11540 | 1333 | 2433.2 | 2300.0 | 1769.55 | 36.51 | 182078 | 280266 | 13344233 | 273 | 6013312 | 1708160 | 2.51 | 2.77 | 2.01 |
| linDef | 256 | 21200 | 2779 | 5738.8 | 4000.0 | 3521.41 | 19.45 | 364794 | 567486 | 27706959 | 545 | 12027736 | 1833748 | 1.99 | 2.08 | 2.00 |
| linLit | 16 | 1630 | 112 | 170.4 | 208.0 | 180.65 | 9.01 | 22203 | 33433 | 1538915 | 35 | 748032 | 1609888 | - | - | - |
| linLit | 32 | 3060 | 233 | 1019.1 | 727.0 | 350.97 | 7.52 | 44989 | 68395 | 3182525 | 69 | 1496024 | 1624024 | 1.94 | 2.08 | 2.03 |
| linLit | 64 | 4850 | 429 | 1583.3 | 978.0 | 762.52 | 17.44 | 90645 | 138649 | 6514965 | 137 | 2994696 | 1652924 | 2.17 | 1.84 | 2.01 |
| linLit | 128 | 11380 | 821 | 3368.5 | 3790.0 | 1644.73 | 23.93 | 181869 | 280107 | 13358625 | 273 | 5989168 | 1718916 | 2.16 | 1.91 | 2.01 |
| linLit | 256 | 20210 | 1446 | 9057.6 | 5270.0 | 3446.78 | 18.16 | 364393 | 567197 | 27763165 | 545 | 11980744 | 1867164 | 2.10 | 1.76 | 2.00 |
| mono | 16 | 1960 | 140 | 221.9 | 220.0 | 211.35 | 11.85 | 22177 | 33133 | 1534649 | 33 | 746416 | 1610248 | - | - | - |
| mono | 32 | 2670 | 138 | 253.7 | 376.0 | 331.57 | 9.11 | 44933 | 67634 | 3169415 | 65 | 1493224 | 1623856 | 1.57 | 0.99 | 2.03 |
| mono | 64 | 5060 | 212 | 617.1 | 833.0 | 718.1 | 10.75 | 90529 | 136697 | 6469401 | 129 | 2989528 | 1649644 | 2.17 | 1.54 | 2.01 |
| mono | 128 | 10280 | 455 | 1268.4 | 1780.0 | 1711.89 | 31.1 | 181633 | 274754 | 13192519 | 257 | 5979264 | 1713256 | 2.38 | 2.15 | 2.01 |
| mono | 256 | 23480 | 1209 | 3052.9 | 4190.0 | 4207.91 | 50.93 | 363917 | 550929 | 27130009 | 513 | 11961368 | 1818808 | 2.46 | 2.66 | 2.00 |

### EvmChain

| variant | N | wall ms | elab ms (wall-based) | elab ms (profiler sum) | kernel ms (prof) | kernel ms (recheck all) | max decl kernel ms | DAG (all decls, shared) | DAG sum | tree sum | decls | .olean B | RSS KB | x2 kernel | x2 elab | x2 DAG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| balDef | 16 | 1260 | 382 | 657.4 | 38.3 | 27.56 | 4.91 | 4156 | 7102 | 104682 | 24 | 191040 | 1665864 | - | - | - |
| balDef | 32 | 1720 | 438 | 2180.3 | 90.2 | 53.83 | 5.16 | 7549 | 13896 | 226038 | 44 | 309632 | 1684972 | 1.95 | 1.15 | 1.82 |
| balDef | 64 | 2780 | 747 | 5368.2 | 241.0 | 116.01 | 6.45 | 14469 | 27897 | 536982 | 84 | 551096 | 1703172 | 2.16 | 1.71 | 1.92 |
| balDef | 128 | 5340 | 918 | 12114.7 | 548.0 | 330.46 | 25.25 | 28165 | 56732 | 1385090 | 164 | 1029296 | 1766384 | 2.85 | 1.23 | 1.95 |
| balDef | 256 | 10010 | 2367 | 23715.2 | 1150.0 | 499.72 | 13.3 | 55715 | 118666 | 4047714 | 324 | 1990912 | 1921680 | 1.51 | 2.58 | 1.98 |
| balLit | 16 | 1470 | 482 | 807.5 | 45.9 | 31.82 | 4.45 | 4107 | 7078 | 104756 | 24 | 187288 | 1665220 | - | - | - |
| balLit | 32 | 1550 | 407 | 1872.8 | 73.6 | 52.12 | 4.66 | 7469 | 13881 | 226846 | 44 | 303496 | 1681136 | 1.64 | 0.84 | 1.82 |
| balLit | 64 | 2900 | 757 | 5474.6 | 160.0 | 115.59 | 5.85 | 14327 | 27901 | 540872 | 84 | 540192 | 1712448 | 2.22 | 1.86 | 1.92 |
| balLit | 128 | 4870 | 940 | 11778.4 | 393.0 | 217.41 | 7.19 | 27899 | 56769 | 1401342 | 164 | 1008856 | 1776372 | 1.88 | 1.24 | 1.95 |
| balLit | 256 | 10670 | 2498 | 28274.0 | 1070.0 | 566.12 | 13.37 | 55201 | 118770 | 4113332 | 324 | 1951400 | 1938708 | 2.60 | 2.66 | 1.98 |
| linDef | 16 | 1340 | 429 | 747.3 | 39.9 | 27.53 | 4.58 | 4157 | 7094 | 104652 | 24 | 191072 | 1666296 | - | - | - |
| linDef | 32 | 1890 | 617 | 2233.9 | 92.3 | 79.26 | 8.19 | 7551 | 13889 | 225986 | 44 | 309696 | 1683136 | 2.88 | 1.44 | 1.82 |
| linDef | 64 | 2660 | -28 | 7127.9 | 161.0 | 117.29 | 6.44 | 14473 | 27892 | 536924 | 84 | 551224 | 1722628 | 1.48 | -0.05 | 1.92 |
| linDef | 128 | 5460 | 1223 | 12820.6 | 573.0 | 216.46 | 5.83 | 28173 | 56731 | 1385058 | 164 | 1029552 | 1759080 | 1.85 | -43.68 | 1.95 |
| linDef | 256 | 9370 | 2190 | 22961.1 | 921.0 | 507.15 | 8.29 | 55731 | 118673 | 4047772 | 324 | 1991424 | 1909336 | 2.34 | 1.79 | 1.98 |
| linLit | 16 | 1220 | 420 | 672.9 | 37.1 | 27.6 | 5.59 | 4108 | 7070 | 104678 | 24 | 187320 | 1665280 | - | - | - |
| linLit | 32 | 1660 | 554 | 2267.6 | 81.1 | 52.74 | 5.19 | 7472 | 13874 | 226394 | 44 | 303592 | 1682036 | 1.91 | 1.32 | 1.82 |
| linLit | 64 | 2490 | 748 | 4487.6 | 186.0 | 132.9 | 11.03 | 14334 | 27896 | 538886 | 84 | 540416 | 1703504 | 2.52 | 1.35 | 1.92 |
| linLit | 128 | 4520 | 948 | 11373.5 | 354.0 | 229.86 | 10.4 | 27914 | 56768 | 1393178 | 164 | 1009336 | 1766820 | 1.73 | 1.27 | 1.95 |
| linLit | 256 | 10390 | 1922 | 25850.2 | 1200.0 | 561.93 | 19.06 | 55232 | 118777 | 4080518 | 324 | 1952392 | 1935480 | 2.44 | 2.03 | 1.98 |
| mono | 16 | 1480 | 639 | 591.6 | 30.7 | 27.35 | 7.16 | 4030 | 5989 | 97424 | 20 | 180912 | 1665336 | - | - | - |
| mono | 32 | 2500 | 1427 | 1351.9 | 66.0 | 69.19 | 12.03 | 7312 | 11190 | 203398 | 36 | 292368 | 1683036 | 2.53 | 2.23 | 1.81 |
| mono | 64 | 3970 | 2308 | 2264.9 | 159.0 | 106.62 | 23.65 | 14010 | 21729 | 460800 | 68 | 519656 | 1715092 | 1.54 | 1.62 | 1.92 |
| mono | 128 | 10010 | 6101 | 6215.5 | 405.0 | 439.05 | 124.84 | 27262 | 42660 | 1117926 | 132 | 969512 | 1774940 | 4.12 | 2.64 | 1.95 |
| mono | 256 | 16170 | 11458 | 11605.4 | 611.0 | 335.37 | 100.0 | 53924 | 84683 | 3050944 | 260 | 1874424 | 1915260 | 0.76 | 1.88 | 1.98 |

### EvmJoin

| variant | N | wall ms | elab ms (wall-based) | elab ms (profiler sum) | kernel ms (prof) | kernel ms (recheck all) | max decl kernel ms | DAG (all decls, shared) | DAG sum | tree sum | decls | .olean B | RSS KB | x2 kernel | x2 elab | x2 DAG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| inline | 16 | 6400 | 4893 | 4814.9 | 127.0 | 93.84 | 23.33 | 14422 | 21912 | 617700 | 68 | 536632 | 1761376 | - | - | - |
| inline | 32 | 7790 | 5848 | 5785.1 | 166.0 | 141.58 | 38.57 | 17317 | 26983 | 768790 | 86 | 636464 | 1798516 | 1.51 | 1.20 | 1.20 |
| inline | 64 | 12200 | 9177 | 9138.6 | 305.0 | 324.06 | 49.66 | 30793 | 49289 | 1447607 | 159 | 1097176 | 1881540 | 2.29 | 1.57 | 1.78 |
| inline | 128 | 22020 | 15524 | 15487.8 | 790.0 | 1131.69 | 215.98 | 49892 | 81354 | 2675786 | 266 | 1751592 | 2061332 | 3.49 | 1.69 | 1.62 |
| inline | 256 | 48920 | 35400 | 35594.9 | 1610.0 | 1228.88 | 270.42 | 95674 | 157628 | 6539590 | 518 | 3318584 | 2427064 | 1.09 | 2.28 | 1.92 |
| perblock | 16 | 4950 | 2563 | 6409.9 | 248.0 | 207.38 | 17.21 | 14027 | 33982 | 668168 | 78 | 534168 | 1751112 | - | - | - |
| perblock | 32 | 5050 | 2734 | 6649.8 | 378.0 | 189.32 | 11.17 | 15841 | 37416 | 742622 | 84 | 595128 | 1752336 | 0.91 | 1.07 | 1.13 |
| perblock | 64 | 6180 | 2855 | 8226.2 | 507.0 | 295.81 | 14.04 | 25854 | 61396 | 1283096 | 126 | 936008 | 1771664 | 1.56 | 1.04 | 1.63 |
| perblock | 128 | 9180 | 4155 | 13970.7 | 754.0 | 452.74 | 30.44 | 39475 | 92188 | 2143166 | 180 | 1398576 | 1805628 | 1.53 | 1.46 | 1.53 |
| perblock | 256 | 21200 | 8035 | 31640.9 | 2340.0 | 1199.78 | 50.74 | 73034 | 170967 | 4962008 | 318 | 2540232 | 1905944 | 2.65 | 1.93 | 1.85 |
| shared | 16 | 4840 | 3439 | 3603.5 | 135.0 | 100.29 | 16.68 | 13429 | 21185 | 494799 | 57 | 502632 | 1745860 | - | - | - |
| shared | 32 | 5870 | 4193 | 4614.7 | 235.0 | 126.29 | 19.76 | 15239 | 24619 | 569253 | 63 | 563360 | 1750328 | 1.26 | 1.22 | 1.13 |
| shared | 64 | 7490 | 5397 | 5756.6 | 280.0 | 213.72 | 28.81 | 25034 | 41139 | 969166 | 96 | 892000 | 1783744 | 1.69 | 1.29 | 1.64 |
| shared | 128 | 9560 | 6777 | 7242.3 | 491.0 | 341.23 | 41.08 | 38575 | 64844 | 1672853 | 143 | 1346728 | 1827404 | 1.60 | 1.26 | 1.54 |
| shared | 256 | 24290 | 16755 | 18197.1 | 1450.0 | 780.97 | 70.26 | 72133 | 122862 | 3921053 | 263 | 2475048 | 1951192 | 2.29 | 2.47 | 1.87 |

### Join

| variant | N | wall ms | elab ms (wall-based) | elab ms (profiler sum) | kernel ms (prof) | kernel ms (recheck all) | max decl kernel ms | DAG (all decls, shared) | DAG sum | tree sum | decls | .olean B | RSS KB | x2 kernel | x2 elab | x2 DAG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| helper | 16 | 5200 | 283 | 1031.0 | 961.0 | 781.1 | 19.37 | 84128 | 128927 | 5980679 | 121 | 2786600 | 1667348 | - | - | - |
| helper | 32 | 6090 | 384 | 1067.7 | 981.0 | 903.6 | 11.27 | 109725 | 167730 | 7821475 | 157 | 3627040 | 1692020 | 1.16 | 1.36 | 1.30 |
| helper | 64 | 12580 | 688 | 2261.9 | 2210.0 | 2178.77 | 28.75 | 213650 | 325256 | 15345665 | 303 | 7039016 | 1758408 | 2.41 | 1.79 | 1.95 |
| helper | 128 | 21040 | 1471 | 3738.4 | 3880.0 | 3414.53 | 44.92 | 365552 | 556169 | 26551995 | 517 | 12026760 | 1875268 | 1.57 | 2.14 | 1.71 |
| helper | 256 | 44180 | 2310 | 7730.3 | 7930.0 | 7599.83 | 82.07 | 724191 | 1099914 | 53742979 | 1021 | 23801760 | 2136056 | 2.23 | 1.57 | 1.98 |
| inline | 16 | 5370 | 326 | 924.7 | 812.0 | 936.92 | 28.37 | 84127 | 128910 | 5980732 | 120 | 2785784 | 1668676 | - | - | - |
| inline | 32 | 6190 | 530 | 1156.7 | 923.0 | 893.38 | 14.12 | 109724 | 167713 | 7821528 | 156 | 3626224 | 1693028 | 0.95 | 1.63 | 1.30 |
| inline | 64 | 12850 | 582 | 2420.3 | 2530.0 | 2326.83 | 30.28 | 213649 | 325239 | 15345718 | 302 | 7038200 | 1761536 | 2.60 | 1.10 | 1.95 |
| inline | 128 | 22690 | 1329 | 3957.4 | 3930.0 | 3857.79 | 51.16 | 365551 | 556152 | 26552048 | 516 | 12025944 | 1871216 | 1.66 | 2.28 | 1.71 |
| inline | 256 | 44620 | 2601 | 7672.2 | 7790.0 | 7479.82 | 106.77 | 724190 | 1099897 | 53743032 | 1020 | 23800944 | 2134480 | 1.94 | 1.96 | 1.98 |
| perblock | 16 | 3660 | 246 | 841.3 | 682.0 | 532.72 | 8.39 | 38177 | 105125 | 4591885 | 113 | 1303376 | 1647372 | - | - | - |
| perblock | 32 | 4250 | 379 | 1501.1 | 919.0 | 623.82 | 8.21 | 44253 | 118077 | 5202009 | 125 | 1504056 | 1651708 | 1.17 | 1.54 | 1.16 |
| perblock | 64 | 7700 | 642 | 2318.0 | 1460.0 | 1482.2 | 30.91 | 72445 | 208757 | 9477677 | 209 | 2448352 | 1687800 | 2.38 | 1.69 | 1.64 |
| perblock | 128 | 16140 | 1592 | 6103.6 | 5540.0 | 2557.26 | 34.1 | 117653 | 325284 | 15013913 | 317 | 3951120 | 1725100 | 1.73 | 2.48 | 1.62 |
| perblock | 256 | 22230 | 2258 | 7173.7 | 5200.0 | 3976.17 | 21.18 | 219264 | 623142 | 29308845 | 593 | 7343272 | 1825752 | 1.55 | 1.42 | 1.86 |
| shared | 16 | 3720 | 212 | 736.4 | 630.0 | 508.49 | 12.54 | 60147 | 94959 | 4293195 | 93 | 2000736 | 1649732 | - | - | - |
| shared | 32 | 4320 | 299 | 1049.5 | 838.0 | 618.53 | 13.63 | 65843 | 107915 | 4903319 | 105 | 2189312 | 1656504 | 1.22 | 1.41 | 1.09 |
| shared | 64 | 7130 | 409 | 1653.8 | 1770.0 | 1075.64 | 14.64 | 100688 | 179474 | 8274829 | 171 | 3341184 | 1695680 | 1.74 | 1.37 | 1.53 |
| shared | 128 | 10890 | 638 | 2346.5 | 2260.0 | 1941.49 | 30.46 | 160852 | 281105 | 13107959 | 265 | 5318160 | 1730800 | 1.80 | 1.56 | 1.60 |
| shared | 256 | 20730 | 1183 | 4221.4 | 4490.0 | 3778.08 | 35.78 | 311697 | 540564 | 25595151 | 505 | 10279200 | 1846632 | 1.95 | 1.85 | 1.94 |

### SolM

| variant | N | wall ms | elab ms (wall-based) | elab ms (profiler sum) | kernel ms (prof) | kernel ms (recheck all) | max decl kernel ms | DAG (all decls, shared) | DAG sum | tree sum | decls | .olean B | RSS KB | x2 kernel | x2 elab | x2 DAG |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| inline | 16 | 7890 | 2197 | 2086.3 | 82.9 | 87.7 | 87.21 | 65359 | 65374 | 10000018 | 3 | 2251216 | 2527452 | - | - | - |
| inline | 32 | 54070 | 28170 | 26612.3 | 1160.0 | 1151.23 | 1150.04 | 621327 | 621342 | 10000018 | 3 | 20325272 | 2678324 | 13.13 | 12.82 | 9.51 |
| inline | 64 | FAILED: ~/evalE/gen/SolM64_inline.lean:83:14: error: Tactic `simp` failed with  |
| inline | 128 | FAILED: ~/evalE/gen/SolM128_inline.lean:147:14: error: Tactic `simp` failed wit |
| inline | 256 | FAILED: ~/evalE/gen/SolM256_inline.lean:275:14: error: Tactic `simp` failed wit |
| shared | 16 | 4630 | 1076 | 1045.2 | 54.5 | 82.63 | 79.26 | 46650 | 46853 | 10018509 | 4 | 1646816 | 2516152 | - | - | - |
| shared | 32 | 25260 | 12633 | 11903.3 | 807.0 | 949.65 | 943.12 | 505450 | 505653 | 10018509 | 4 | 16587304 | 2419072 | 11.49 | 11.74 | 10.83 |
| shared | 64 | FAILED: ~/evalE/gen/SolM64_shared.lean:83:2: error: Tactic `simp` failed with a |
| shared | 128 | FAILED: ~/evalE/gen/SolM128_shared.lean:147:2: error: Tactic `simp` failed with |
| shared | 256 | FAILED: ~/evalE/gen/SolM256_shared.lean:275:2: error: Tactic `simp` failed with |
