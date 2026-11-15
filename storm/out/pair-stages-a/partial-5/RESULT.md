# pair-stages-a: partial 5 (2026-11-15 ~00:15 UTC)

**UniswapV2Pair mint still has no end-to-end stage theorem.** This drop moves
the lane onto the new bases and removes the old mir5 -> sched blocker; the
Sched stage itself does not check yet.

Bases: solidity-lean #166 head f8a4a744, solar #2637 head 902cccc2.

## What changed

Upstream 902cccc2 (82f1a018b) already has scoped stages (\`--cut --joins
--no-mir-joins --exclude\`), pruning and MIR->Sched cuts inside callees with
each caller's words below the call. My earlier solar commits overlapped it, so
they are dropped. On top of it (solar.bundle, 902cccc2..pair-stages-b):

1. 8f74e3fae fix(certify): name kept immediates in the schedule map. The
   scheduler keeps a repeated immediate (mint's MINIMUM_LIQUIDITY 1000) on the
   stack. The exported MIR writes immediates as constants, so the schedule
   map's \`v65\` named no exported value and the relation left that word
   free. Schedule.json now writes such words as \`"c0x3e8"\`, and the generator
   relates them as that constant. Re-exporting changes only Schedule.json:
   every stage file and the bytecode are byte-identical.
2. ed5705c19 fix(certify): relate scheduled blocks at every entry height. The
   static height pass does not follow returns from internal calls. So a shared
   revert block got one height (4) while the configuration graph also enters
   it at 10. Under dynamic jumps, relations now cover every entry height.
3. db20123de fix(certify): name the dispatcher's selector word in scoped EVM
   IR relations. A cut between selector tests left the selector as a free
   word \`w0\`, so the excluded \`transfer\` branch could not be refuted from
   the scope hypotheses. evm_states tracks \`push 0; calldataload; push 224;
   shr\`, and relations name the word \`shr 224 (calldataWord call 0)\`. With
   this, evm1 Seg0 (previously failing) builds.

solidity-lean (sl.bundle, f8a4a744..pair-stages-b):

- a33eed7: lakefile libraries (cs_scope, uv2_pair_mb, uv2_pair_m) and
  \`seg_case_contra\`. The boolean simproc fix of the old lane is dropped,
  because upstream landed the same fix.
- 051dd8a: \`seg_case_contra\` also reduces \`2 == 1 || ...\`, the cut tests of
  numeral blocks.
- de9d352: \`seg_word_eq\` relates \`iszero a\` to \`eq a 0\` (\`rfl\`). The
  scheduler emits ISZERO where MIR has \`eq v, 0\`.

## Pair mint inventory on the new bases

The pair was re-exported with solar 902cccc2 and generated with
\`--cut --joins --no-mir-joins --segment 8\` plus 26 \`--exclude\`, as in
scripts/verify/uniswap_v2_stages.sh. It has 26 EVM IR stages and 5 MIR passes.

| stage | result |
|---|---|
| Mir2, Mir3 (whole-stage, 14 segments each) | **failed**: 13/14 segments whnf timeout at 2M heartbeats. The generated axiom guard then refuses \`mir2_certified\`/\`mir3_certified\` (depends on \`mir2_segments\`), as it should. |
| Mir1, Mir4, Mir5 | not run (same shape; stopped to prioritise Sched) |
| mir5 -> sched (246 segments, 16 files) | before de9d352: Seg0-7, Seg10-12, Seg14 built. Seg8 left 6 open leaves: ISZERO vs \`eq _ 0\`, now handled by de9d352, not yet rebuilt. Seg13 has 1 whnf timeout at 2M. |
| sched -> evm1 | Defs, Seg0 (190 s), Seg1 (92 s), Seg2 (187 s), Seg3 (129 s) built. The rest were not reached. |
| evm2 .. evm26 | not reached on the new bases |

On the old base 9fb89ee, \`evm2_certified\`/\`evm2_certified_back\` checked
with \`#print axioms\` = [propext, Classical.choice, Quot.sound]. That receipt
is **not** re-established on f8a4a744.

No stage-level theorem has a receipt on the new bases yet. Nothing here is
claimed beyond the listed files elaborating.

## Running now

A full rebuild of Sched + Evm1-26 with de9d352 on this Hand (5 cores,
14 GB, 2 jobs). Box quota was full (3 active boxes, others').

## Next

- MIR stages need join cuts for mint (whole-stage runs time out). The
  generated variant with MIR joins gives Mir1 46, Mir2/3 254, Mir4 230 and
  Mir5 456 segments. Mir1 is place-reads, where upstream says joins don't
  hold.
- Sched Seg13 timeout; finish Evm1-26; then Stages.lean and receipts.

