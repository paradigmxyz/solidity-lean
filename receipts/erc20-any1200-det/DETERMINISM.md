# ERC20 cross-slot plan mismatch: cause and evidence

Hosted machine only, no boxes. Lean 4.35.0 (commit eb6cafb, the boxes' toolchain), solidity-lean
1f0db760, candidate solar f71b7554 (166137ef). Built from source because the Mathlib cache hosts were
unreachable from this machine.

## 1. SolidCore.Refinement.Solar.AssembleCallWorld

Not generated, and its import closure (146 modules, 100 local) contains no generated module. Both
slots built it in run.sh with identical dependencies: every other olean of the 4028-module plan
matched. The difference is Lean elaboration nondeterminism (results):

* 7 rebuilds with LEAN_NUM_THREADS 12, 1 and 5: all 2e474eef… (slot 1's olean).
* 10 rebuilds at LEAN_NUM_THREADS=48 with the CPU saturated: 9 x 2e474eef…, 1 x cebc9de8… (stress-2),
  which is slot 2's olean byte for byte.
* 10 rebuilds at LEAN_NUM_THREADS=1 with the CPU saturated: 9 x 2e474eef…, 1 x cebc9de8… (serial-6).
* The two variants (2e474eef, 1243872 bytes; cebc9de8, 1243968 bytes) hold the same 117 constants in
  the same order with equal types and values, and the same 20 environment extensions with equal entry
  counts (olean-diff.txt, from OleanDiff.lean via readModuleData). Only the serialized layout differs.

So no thread setting makes two independent builds byte-identical. The byte-identical-plan rule can
only hold if later slots replay the same olean files as the first slot.

## 2. uv2_erc20.gen.UniswapV2ERC20.Manifest

The stage export (scripts/verify/uniswap_v2_erc20_stages.sh, mktemp -d) records
`-Zemit-lean-stages=/tmp/tmp.XXXXXXXXXX/stages` in manifest.json (arguments, and twice in its
options string) and in Manifest.lean's `arguments`. Two exports here differ only there
(export-diff.txt). Manifest oleans: raw exports 7627e374… vs 0ec21569…; after
normalize_export.py, both ce9d1a8b… (identical). manifest.json also records the host's thread count
(`threads: 4` here), which reaches no olean.

## 3. Harness fix

paradigmxyz/solar alpharush/erc20-any-ship ecc82815472d6ed2d796a2c7bdb940ca370982a0 (parent 2b2c3ddf):
normalize_export.py (run by prep.sh after the export); pack.sh (slot.sh with SHIP_OUT, after run.sh:
archives every non-toolchain olean of the closure, the generated sources and check_final.log);
unpack.sh (slot.sh with PRIOR_SHIP and PRIOR_SHIP_SHA256: no build; refuses with exit 4 unless the
archive's sha256, every archived file, and every planned olean, the toolchain's included, match the
earlier slot's plan). Tested here on a 1714-module closure (ship-test.txt): restore after deletion,
0 mismatched; wrong archive sha256, exit 4; one tampered plan entry, exit 4.

Not shown here: a box run of the new path, and whether the replay fits the slots. 59d0fa44's batches
total about 417 batch-minutes (about 168 min at PAR 4), and each 2 h slot leaves about 70 min of
replay admission before its stop margin, so two slots are still unlikely to finish the replay.
