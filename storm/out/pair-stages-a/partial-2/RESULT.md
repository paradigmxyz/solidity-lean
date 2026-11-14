# pair-stages-a: partial status 2 (2026-11-14 ~16:40 UTC)

**No stage theorem for UniswapV2Pair's mint is proved yet.** What is proved
is the scoped cut-point pipeline end to end on Math.sqrt: the v2-core
`Math.sqrt` source (as port.py writes it) behind CallSqrt's entry `f`, with
the other entry `g` left out by the `scope` premise. This is not the sqrt
code as compiled inside the Pair: there it is inlined and scheduled with mint.

## What checks: cs_scope (Math.sqrt, scoped)

Theorems (namespace `SolarTV.Milestone.CsScope`):

    cs_scope_mir_to_evmir (o : Oracle) :
      Stage (mirSem o) (evmirSem o) CallSqrt.stage0 CallSqrt.evm13 scope
    cs_scope_certified, cs_scope_certified_back      (Stages.lean)
    cs_scope_bytecode (o) (ho : cert.env = true → OracleOk o)
      (hr : cert.reads = true → EnvOk o) (gas) :
      Within (mirSem o) (ethLibWith gas) CallSqrt.stage0 code scope
    cs_scope_bytecode_run : WithinRun mirSem (fun _ => stage0) code scope (CertOk cert)
    scope := fun call => shr 224 (calldataWord call 0) ≠ 0xe420264a   -- g(uint256)

Every stage (stage0 -> mir1 -> sched -> evm1 ... evm13) is a generated cut-point
simulation checked by `sym_seg`. No hand model of the program.

Receipts (this Hand: 5 cores, 14 GB; `LEAN_NUM_THREADS=2 lake -KleanMemory=6000`):

- `lake build cs_scope callsqrt`: **EXIT 0** after 813 s (both libraries,
  callsqrt rebuilt as a regression check of the Segment change). Peak RSS
  2,450 MB (cs_scope Execution.lean); Sched 1,924 MB; each Evm stage <= 1.9 GB,
  33-61 s.
- `#print axioms` of all five theorems above: `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit` or `axiom` in cs_scope's generated files (grep: 0).
- Negative controls, both refused by execution of the build:
  - A: evm7 with one `push 1` changed to `push 2` (copied library cs_negA):
    `lake build cs_negA.Proofs.Runs.Evm7` EXIT 1, "sym_seg: the segments end
    differently on this path" on the edited segments.
  - B: runtime bytecode with its second byte changed (cs_negB):
    `lake build cs_negB.Proofs.Assembly` EXIT 1, `decide` proves the item walk
    false and the #guard_msgs checks fail.

Reproduce (on solidity-lean 9fb89ee + sl.bundle, solar from solar.bundle):

    cp -r Certified/callsqrt/gen Certified/cs_scope/gen     # identical to the tracked stages
    cd Certified/cs_scope && python3 <solar>/tools/certify/certify.py gen/CallSqrt \
      --gen-module cs_scope.gen.CallSqrt --proof-dir Proofs --proof-module cs_scope.Proofs \
      --namespace SolarTV.Milestone.CsScope --label cs_scope --exclude e420264a='g(uint256)'
    # Proofs.lean imports Proofs.Stages, Proofs.Assembly, Proofs.Execution (as callsqrt's)
    lake build cs_scope

## Pair mint: where it stands

Generated with `--joins --arms` (new: also cut at branch arms of kept
functions, so a segment runs at most one branch): about 130 segments per MIR
stage, 83 for Sched, 51-156 per EVM stage. Building now (Mir1-5, Evm1-26).

Failing so far (8M heartbeats each):

- Sched: `sched_seg31` (from sqrt's loop exit in mint's call, through sub
  and _mint back to mint) times out. The cause: the generator's MIR->Sched
  relation cannot cut inside a called function unless the scheduler records
  the return address in the block's layout ("no return address at the loop
  header of N" for _update, _mint and the others), so Sched segments carry
  whole callee bodies; _update has 60 blocks. Fixing this needs a relation for
  a return address held below the recorded layout. This is the blocker for
  the mir5 -> sched link.
- Mir1: `mir1_seg99` (entry of _update, block 0) and `mir1_seg118` (the
  runtime entry: selector dispatch over 27 selectors with 26 scope
  exclusions) time out.
- Earlier: mint's revert-bubbling and _mint paths (old seg9/seg10) were
  slow, not stuck: case splits through checked adds and keccak-slot storage
  updates grow the terms; arm cuts now end those segments early.

Fixed on the way (in sl.bundle): boolean literal simprocs claimed
`a || false = a` definitionally (kernel rejected); `seg_case_contra`
closes cut-test cases that contradict each other.

## Not in this lane

E5 for mint (staticcalls: returndatasize lies outside the executed
fragment); burn and the other 25 external functions, excluded by `scope`.

## Bundles

- `solar.bundle`: 38b5232ad..pair-stages-a (4 commits; adds --arms/--segment).
- `sl.bundle`: 9fb89ee..pair-stages-a (3 commits). Generated pair and
  cs_scope files are not committed (GPL-derived sources).

