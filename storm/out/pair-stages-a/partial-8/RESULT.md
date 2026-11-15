# pair-stages-a partial-8: UniswapV2Pair `mint`, tactic fix for stack checks and operand order

Bases unchanged: solidity-lean f8a4a744, solar 902cccc2 + pair-stages-b
(partial-5). New solidity-lean commit e4216d9 on pair-stages-b (patches/0004;
patches/0001-0004 are the full series on f8a4a744).

## What changed (patches/0004, tv/W1Proofs/Segment.lean)

- `iteNatCmp` simproc. Once the stack height is known, the EVM stack-depth checks
  (`stack.length + 1 > 1024`) become `if 15 > 1024 then ...`. The decision
  instance still names the unevaluated height (`Nat.decLt 1024 l.length`), so
  simp's `ite` congruence can't use `Nat.reduceGT`/`reduceIte`, and `sym_cond`
  split on every such check. The simproc rewrites the whole conditional with
  `ite_cond_eq_false`/`ite_cond_eq_true` and a `decide` proof on the numerals.
  It is in `seg_cut_test`'s simp set, so the checks go before `sym_cond` runs. The
  earlier `dsimp` attempt (partial-6 notes) ran the kernel out of memory. This one
  stays under 2.8 GB per segment.
- `seg_word_eq` after `sym_norm`: `simp only [evm_iszero_eq, evm_gt_lt, evm_eq_comm]`.
  `evm_iszero_eq` only applied before `sym_norm` resolved the `Env.set` lookups, so
  the Sched Seg8 leaves never saw it. `evm_gt_lt : gt a b = lt b a` is rfl.
  `evm_eq_comm` is a permutation lemma, which simp applies in term order.
- Checked: the patched Segment.lean elaborates against the existing build (exit 0).

## Leaf tests (leaf-tests/results.txt)

Each previously failing segment theorem was compiled alone with the same tactics
(leaf-tests/scratch-tactics.lean, which has a `sym_seg2` copy and a debug helper),
maxHeartbeats 2000000, `lean -M 6000`, followed by `#print axioms`.

- 25 segments with open leaves (Sched Seg8 x6, Seg9:522/556; Evm4-Evm11): all close.
  Axioms are propext and Quot.sound, sometimes with Classical.choice. 130-180 s and
  2.3-2.7 GB peak each for the EVM ones, 8-16 s for Sched.
- 14 segments that timed out: 8 now close (Evm2 Seg0:15, Seg6:525, Seg7:15; Evm3
  Seg3:185/219; Evm5 Seg3:151, Seg6:151/185). 6 still time out at 2M heartbeats:
  Evm2 Seg4:355/389, Evm5 Seg3:185, Sched Seg9:389/423, Sched Seg13:83.

## Build runs

- b_evm7 (old tactic) died at Evm13 when the Hand paused, with no exit line.
- b_evm8 (old tactic, Evm12-26) was stopped at Evm18 to switch tactics. It built
  97 modules (built-b_evm8.txt). Failures (failing-b_evm8.txt): Evm12 Seg6:80/114
  open; Evm13-Evm18 Seg6:49/83 time out. These look like the same stack-check
  pattern, but they are not tested yet with the new tactic.
- b_full9 (new tactic, Sched + Evm1-26, 386 targets) started at 07:47 UTC. Every
  proof module rebuilds, because Segment.lean changed. Its exit code and memory
  go in partial-9.

## Status

Only `evm1_certified` has a checked stage theorem (partial-6, on the old tactic).
It is re-checked in b_full9. `mint` has no end-to-end theorem. That still needs
the 6 timeouts above fixed (next: `--segment 4` for those segments), Evm12-26
confirmed, and the MIR stages (MIR join cuts; Mir2/Mir3 timed out earlier).
