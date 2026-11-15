# pair-stages-a: partial 6 (2026-11-15 ~02:00 UTC)

**First UniswapV2Pair (mint) stage theorem on the new bases:** sched -> evm1
(EVM IR pass \`peephole-early\`), both directions, under the mint scope.
**There is still no end-to-end mint theorem.** Sched, the MIR stages and most
EVM stages do not check yet.

Bases: solidity-lean #166 f8a4a744, solar #2637 902cccc2, plus the bundles
in partial-5. Unchanged since then.

## Checked

    SolarTV.Milestone.Uv2PairM.evm1_certified (o : Oracle) :
      Certified EVM.Program.layer EVM.Program.layer o UniswapV2Pair.sched UniswapV2Pair.evm1 scope
    SolarTV.Milestone.Uv2PairM.evm1_certified_back (o : Oracle) :
      Certified EVM.Program.layer EVM.Program.layer o UniswapV2Pair.evm1 UniswapV2Pair.sched scope

Here \`scope call\` means the call's selector word \`shr 224 (calldataWord call 0)\` is
none of the 26 other external functions' selectors (axioms-evm1.txt lists the
whole premise).

- \`#print axioms\`: both depend only on [propext, Classical.choice, Quot.sound]
  (axioms-evm1.txt).
- No \`sorry\` in Runs/Evm1.lean, Runs/Evm1/Defs.lean or Seg0-Seg7 (grep counts 0).
- Built by \`lake -KleanMemory=6000 build uv2_pair_m.Proofs.Runs.Sched
  uv2_pair_m.Proofs.Runs.Evm1 ... Evm26\` (LEAN_NUM_THREADS=2, this Hand:
  5 cores, 14 GB). The module and its 8 segment files elaborated within
  6 GB each; the files took 92-190 s.
- The whole-target exit code is still pending, because the build is still
  running. A negative control for this stage (an edited evm1 constant) is not
  run yet.

## Inventory at the current tactic state (de9d352)

Built: Sched Defs, Seg0-7, Seg10-12, Seg14; Evm1 (whole stage); Evm2 Seg1-3,
Seg5; Evm3 Seg1, Seg2, Seg7; Evm4 Seg1, Seg2, Seg4-7; Evm5 Seg0, Seg1, Seg4,
Seg5, Seg7.

Failing (theorem at file:line):

- Sched: Seg8:284/318/352/386/420/454 open leaves (ISZERO vs \`eq _ 0\` in one
  traced leaf; de9d352's leaf step did not close them); Seg9:389/423
  timeouts, Seg9:522/556 open leaves; Seg13:83 timeout.
- Evm2: timeouts at Seg0:15, Seg4:355/389, Seg6:525, Seg7:15.
- Evm4: Seg3:216/250 open leaves.
- Evm5: Seg2:454/488 and Seg3:46/80 open leaves; timeouts at Seg3:151/185
  and Seg6:151/185.
- Mir2/Mir3, whole stage: 13/14 segments time out (partial-5). Mir1/4/5 not run.

## Finding: why evm5_seg48 stays open

Its evaluation stops at an EVM IR step's stack limit \`if 15 > 1024 then …\`.
\`sym_eval\` is \`dsimp\`, which has no rule for a literal \`>\` on Nat.
\`sym_cond\` (\`simp only [*, …, Nat.reduceGT]\`) would decide it, but on this
goal it hits simp's step limit. I extended Segment's \`iteNatLit\` dsimproc to
decide \`<\`, \`>\`, \`≤\`, \`≥\` of numerals. All leaves then closed, but the
kernel ran out of memory (6 GB) checking the definitional step. That change
is reverted, not shipped. Options: a proof-producing step for these
conditions inside the matcher, or smaller EVM segments (\`--segment 4\`).

## Capacity

This Hand builds about 10 proof files per 10 min. The pair has about 460
files, so it needs about 7 h. The box quota stayed full all night (3 active
boxes, others'), and a freed slot went to another lane. Built oleans persist
on the Hand, so the build resumes across turns.

