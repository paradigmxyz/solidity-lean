# refuter-6 result (round 3: solar 902cccc2c, solidity-lean f8a4a74)

Still strongest at 902cccc2c: R1, R1b, R4, R5, R6, R10, and the committed bank and verify_token
shapes (R4b gas above the tx cap, H1 universal hash premise). Fixed: R8. R9 labels "proved" without
strongest. Transfer (f8a4a74): sound for caller 0x2000 with the scoped premise; gaps T1 (caller
fixed), T2 (no Allowed witness), T3 (not through the driver). Details: REPORT.md.

Deliverables here:
- sl-refuter6-v3.bundle: solidity-lean branch refuter6/v3, prerequisite f8a4a74. lean_lib Refute6:
  Model, Variants, Shadow, Open, Proof, SkipKernel (kernel-unchecked on purpose), Axioms; harness
  Refute6/variant2.sh, Refute6/v3-runs.sh, Refute6/rtime.py; R10 shim sources Refute6/r10/; all run
  outputs with receipts under Refute6/out/ (v3-* this round, v2-* the driver-lane round).
- solar-refuter6-v3.bundle (prerequisite 902cccc2c, branch refuter6/r10-fix) and
  patch/0001-fix-certify-run-the-checkers-without-lake-env-s-load.patch: the R10 fix, bash -n
  checked, exercised by v3-r10-fix-control (refused). Not run as a full scripts/certify.

Receipts:
- `LEAN_NUM_THREADS=1 lake -R -KleanMemory=6000 build Refute6.Proof Refute6.Model Refute6.Shadow
  Refute6.SkipKernel Refute6.Axioms counter.gen.Counter.Bytecode Contracts.Counter.ShapeExport`:
  exit 0, peak RSS 2905 MB, 105 s.
- `#print axioms`: every Refute6 theorem [propext, Classical.choice, Quot.sound] or a subset; no sorry.
- solar 902cccc2c `cargo build --locked --bin solar` + `-p solar-verify`: exit 0, peak 1469 MB.
- Variant runs (v3-*.out): exit 0 and strongest=True for baseline, R1, R1b, R4, R5, R6, R10 (full
  closure replay); exit 1 "refused by the kernel replay" for R8 planted bin, the unchecked-proof
  control and the R10 fix control; exit 0 strongest=False for R9. Each lean with -M 6000.

Missing: a full scripts/certify run printing CERTIFIED for a variant (the harness runs step 6b with
the driver's own tools); the transfer slice through the driver (no shape.json exists).
