# ERC20 ACCEPTANCE-1200 READMIT: ACCEPTED

Runtime tier only. No no-OOG claim. Not universal end-to-end. TargetPostAt holds only under the
conditional, finite ScopeAt premise (Keccak-256 separation of the caller's and recipient's balance
preimages); this is not universal Keccak separation.

## Verdict

merge.py exit 0: "merged: 4028 of 4028 modules replayed exactly once, 0 trusted; per slot {1: 400,
2: 2428, 3: 1200}; inventory 5003602200cc5d064512370dbc3581677c41f78fbc75d4576bc44dd099a3a71a".
One plan for every slot: a77d7bd5b26c50ae10fdd627e09e71b8234070771cc152735bdf057ba0e342af
(batches 7d402409… in every slot). Each module is credited once, to the slot and batch that
replayed it (merge-receipt lists all 4028). No fourth slot.

| slot | box | batches replayed (exit 0) | modules |
| --- | --- | --- | --- |
| A | erc20ra-47fd (FRA) | 3600 | 400 |
| B | erc20rb-4377 (FRA) | 1200, 1600, 2000, 2400, 2800, 3200, 4000 | 2428 |
| C | erc20rc-dba6 (FRA2) | 0, 400, 800 | 1200 |

Slot A's 2400 and 2800 were killed at its deadline (not credited) and replayed in slot B. Slot C's
prior (priorC/) is slot B's out/replay with its batch-exits line for batch 3600 replaced by slot A's
("3600 0 151343792 ran"), because sched.py skips only prior batches marked "ran"; plan and batches
are byte-identical to every slot's. Slot C's own replay.sh ends "partial slot" (exit 2) by design;
merge.py is the cross-slot account.

## Authority

AUTHORITY.txt. READMIT tempoxyz/solar-verification-archive coordinator/receipts @ 4ec3f803,
receipts/ERC20-1200-READMIT.md (sha256 71ac4137): at most 3 sequential m4-metal-large 2 h slots.
Release, verbatim: Troy Sargent, 15:04 CST Nov 26, thread 2ee861d1: "don't do hourly runs just run
it now and keep going all the way". Interpretation (coordinator, stated separately): taken as
releasing slots B and C within the 3-slot cap; not an explicit three-slot or nondeterminism ruling.

## Pins

package 41e6b29b; gates 1f0db760 (Statement.lean a8473b23…7a9c); overlay 4332b47d only
(TransferExpected 8573c694…988c); slice 902cccc2; harness solar ecc82815 (alpharush/erc20-any-ship,
parent 2b2c3ddf); solar f71b7554, -Ogas --evm-version osaka. Candidate binary: old pin
15808eeef2f5d5d021372d43a36ef491492cc8b2fc84b2c3b97a666a736381db (unreproducible: embedded build
timestamp), new pin 166137ef66c1d792afd5b39bf5e3a1b02402f6c4484032f8b4115d926dd1245a (environment
override of CANDIDATE_SHA256 only; same commit, tree caad2955, lock eb1a7cf2, rustc 1.100.0).

## Bindings (slot A build)

* Fresh emit: 1200 runtime bytes, sha256 31f5c33cf15e660cf99ef9a9629a3b09fd48cb93fb983ad128d423f7ce11b420
  (gen.py: equal to Statement's runtimeBytes; 18 stages; 3 stage sources).
* check_final: "Certified.erc20_any.Final.final : Certified.erc20_any.Final.Statement (module
  erc20_any.Statement, which does not import erc20_any.Proof); axioms [propext, Classical.choice,
  Quot.sound]". Statement includes every-real-caller satisfiability, the finite footprint, and
  Expected for specAny and specScoped; the sequential self-transfer and the checked overflow are
  decided in SeqPostAt.
* Export: raw-export/ (unnormalized, from the pinned binary) and norm-export/ (the run's,
  normalized by prep.sh). They differ only in -Zemit-lean-stages=/tmp/tmp.99ruyzPzlc/stages vs
  EXPORT/stages (manifest.json arguments and options; Manifest.lean arguments); export-diff.txt.
  Every stage file is identical; sources, compiler and pinned options unchanged.
* Negatives (slot A, all OK): control pass; byte_first, byte_last, source_pins, source_contract,
  prop_credit_plus_one, prop_self_no_overflow, prop_unchecked_overflow, ctx_self_caller,
  gas_minus_one, footprint_dropped, gen_mutated_emit (fresh-byte mutation), src_stage_safemath,
  src_stage_erc20 each fail.

## Ship (build once, replay elsewhere)

ship.tar 7bdc19a839df208ccaf51f7b5ef153e6392fed2c2bbdf06bc2a542704606a3c8 (1793392640 bytes;
files list ead5ea6a…). Staged through the hosted Hand as ship.tar.zst
e87e5d894c5381bd0c2e77bb6fd022c1e7d51d763d7c650a7602d94d15d16d76 in parts part.00 e85eef66…,
part.01 ed82a570…, part.02 2e3d566a…. Verified on box A (written), hosted (parts OK, decompressed
tar 7bdc19a8), box B and box C (parts OK, rebuilt tar 7bdc19a8; ship.box.sha256). unpack.sh precheck
in B and C: planned 4028, mismatched 0.

## Memory (raw cgroup memory.peak bytes; memory.events oom, oom_kill, max all 0)

A: core 4553928704, slice 3771940864, run 12919943168, pack 1858134016, verify 2916573184,
unit (system.slice/erc20-slotA.service, replay inside) 171880570880.
B: unpack 2003918848, unit 209023721472. C: unpack 2003148800, unit 39554310144.
Raw files in A/cgraw, B/cgraw, C/cgraw. Every build_cap gate line PASS; 0 FAILED lines in all slots.
