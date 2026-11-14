# refuter-6 result

Deliverable: REPORT.md (R1, R1b, R4, R4b, R5, R6, R8, R9 reproduced; R7, H1, F1 by reading).

Checked:
- sl-refuter6.bundle: solidity-lean branch refuter6/head, prerequisite d5daff5
  (alpharush/certified-translation). Adds lean_lib Refute6 (lakefile) and Refute6/{Model, Variants,
  Shadow, Open, Proof, SkipKernel}.lean, the harness Refute6/variant.sh and r9.out.
  `lake -KleanMemory=6000 build Refute6.Proof`: exit 0 (2721 jobs), LEAN_NUM_THREADS=1.
  Theorems (namespace SolidCore.Refinement.Solar.Counter.Refute6): restrict, raise, published_huge,
  published_one, post_rejects1, allowed_rejects1, nonvacuous_one, published_open, nonvacuous_open;
  axioms propext, Classical.choice, Quot.sound. Refute6/SkipKernel.lean is the hostile module of R8
  (kernel-unchecked on purpose; the toolchain's leanchecker refuses it).
- Variant runs: `Refute6/variant.sh LEAN_DIR SOLAR_DIR counter Counter LABEL 'EDIT'` with SOLAR_DIR at
  solar 38b5232ad; exit 0 and `strongest=True` for R1, R1b, R4, R5, R6 and R8 (planted checker);
  exit 1 "refused by the kernel replay" for R8's control; exit 0, labels "proved", strongest False
  for R9. Outputs under wip/ (pre-reset bundle, Refute6/harness/*.out) and r9.out.
- Memory: every Lean process capped at -M 6000 (peak not measured) on a 14 GB Hand.

Earlier full-driver run (pre-reset, storm/solar-sq): R1 passed steps 1-6b through check_final; the
kernel replay did not finish before the Hand paused, so no full-driver CERTIFIED line was captured.

Missing: a full scripts/certify run printing CERTIFIED for one variant (about 40 min with
CERTIFY_CLEAN_BUILD=1); fixes are proposals, not patches.
