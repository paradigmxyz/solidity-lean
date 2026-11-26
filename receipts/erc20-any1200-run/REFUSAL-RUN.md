# ERC20 ACCEPTANCE-1200 run: INCOMPLETE-REPLAY REFUSAL

Runtime tier only. No no-OOG claim. Not universal end-to-end. This is not an acceptance.

## Verdict

The kernel replay of the closure was not completed: 0 of 4028 planned modules replayed, 4028
unverified. merge.py refused (exit 1): "merge refused: the slots' plans differ: their builds'
oleans are not identical, so no slot's replay counts". Per the admission, no slot was added and
nothing was retried.

Why:
* Slot 1 admitted no replay batch: its build ended 18:35:47Z, after REPLAY_STOP_AT (deadline minus
  50 min = 18:27:40Z). replay.sh exit 2, "partial slot".
* Slot 2 refused to replay (replay.sh exit 3, "inventory mismatch with ~/prior/replay: the earlier
  slot's replay is void"). Its plan differs from slot 1's in two of 4028 modules:
  uv2_erc20.gen.UniswapV2ERC20.Manifest (olean 6a1173d2… vs bc86adf1…) and
  SolidCore.Refinement.Solar.AssembleCallWorld (2e474eef… vs cebc9de8…).
  The stage export records its temporary directory in its arguments
  (`-Zemit-lean-stages=/tmp/tmp.XXXXXXXXXX/stages`), so manifest.json and Manifest.lean differ on
  every run (slot 1 3ccb133f…/4116fc04…, slot 2 24f001b3…/105b9589…), and the harness's
  byte-identical-plan rule cannot hold across two slots that each regenerate the export. Every
  other generated input (prep/inputs.sha256, 68 files) is identical between the slots.
  Slot 2's build ended 19:15:34Z, before its stop-at (19:56:26Z), so it had time to replay.

## Pins

| | |
| --- | --- |
| package | solidity-lean 41e6b29b (ACCEPTANCE-1200.md) |
| gates | solidity-lean 1f0db760 |
| overlay | TransferExpected.lean from 4332b47d, sha256 8573c694…988c |
| slice | solar 902cccc2 |
| harness | solar 2b2c3ddf (tools/certify/erc20_any, unmodified) |
| compiler | solar f71b7554, -Ogas --evm-version osaka |
| candidate pin, old | 15808eeef2f5d5d021372d43a36ef491492cc8b2fc84b2c3b97a666a736381db |
| candidate pin, new | 166137ef66c1d792afd5b39bf5e3a1b02402f6c4484032f8b4115d926dd1245a (environment override of CANDIDATE_SHA256 only) |

Re-pin ruling (coordinator, Nov 26, under the admission): 15808eee cannot be reproduced because the
binary embeds VERGEN_BUILD_TIMESTAMP (an earlier clean rebuild also differed, aef10850). The new
binary is the same commit f71b7554, src tree caad2955, Cargo.lock eb1a7cf2, rustc 1.100.0
(0ef1bc386 2026-11-09), the same paths, RUSTFLAGS unset, clean tree (build receipt at b7dfb27b).
Acceptance binds the emitted bytes.

## What each slot did show (not acceptance)

* Fresh emit, both slots: 1200 runtime bytes, sha256
  31f5c33cf15e660cf99ef9a9629a3b09fd48cb93fb983ad128d423f7ce11b420, equal to Statement.lean's
  runtimeBytes (gen.py checked; artifacts.sha256: Statement.lean a8473b23…7a9c).
* Export manifest (slot 2, export-manifest.json, sha256
  24f001b388b11141ff1ab7c1a135783a423f9c2fd282d8dc24e77a19bbe181ad): compiler
  0.8.38+commit.f71b7554.solar.0.3.0-dev, 18 stages, optimization Gas; Statement pins the 18
  stage sha256s.
* check_final, both slots: "Certified.erc20_any.Final.final : Certified.erc20_any.Final.Statement
  (module erc20_any.Statement, which does not import erc20_any.Proof); axioms [propext,
  Classical.choice, Quot.sound]". Statement includes every-real-caller satisfiability, the finite
  footprint conjunct, and Expected for specAny and specScoped. The sequential self-transfer and
  overflow are decided inside SeqPostAt; TargetPostAt is CONDITIONAL on ScopeAt (Keccak separated on
  the caller's and recipient's balance preimages only), not universal Keccak separation. These are
  elaborated, not kernel-replayed.
* Negatives (slot 2, out/neg/results): control pass; byte_first, byte_last, source_pins,
  source_contract, prop_credit_plus_one, prop_self_no_overflow, prop_unchecked_overflow,
  ctx_self_caller, gas_minus_one, footprint_dropped, gen_mutated_emit (fresh-byte mutation),
  src_stage_safemath, src_stage_erc20 each fail as required (all OK).
* Build gates: every build step in both slots exit 0 and PASS, oom_kill=0 on all 12 step lines,
  memory.max 303929683968 read back, swap 0. Peak cgroup tree (peak_tree_kb), slot 1: port 154816,
  verify 2848392, core 4407680, slice 3620456, prep 168540, run 10904196; slot 2: port 150916,
  verify 2828848, core 4466236, slice 3620064, prep 90316, run 12351160.

## Boxes

Slot 1 erc20s1-387d (m4-metal-large FRA), created 17:17:40Z, destroyed after copy-off.
Slot 2 erc20s2-b235 (m4-metal-large FRA2), created 18:46:26Z after slot 1 was destroyed,
destroyed after copy-off. Never two at once. Copy-off tree hashes matched both sides
(slot1 74b52c7d…, slot2 b3a70800…).
