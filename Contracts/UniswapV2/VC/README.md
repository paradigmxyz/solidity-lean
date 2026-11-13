# Uniswap V2: solar-verify's verification conditions in the kernel

v2-core is GPL-3.0, so this directory keeps no port, export or proof of it: `discharge.sh` writes
them under an output directory at build time from solar's `solar-tv/uniswap-v2/port.py` and
`crates/verify/uniswap-v2/` (specs and `apply_specs.py`), and runs
[Verify/Discharge/discharge.sh](../../../Verify/Discharge/discharge.sh) on each contract's export:

```text
Contracts/UniswapV2/VC/discharge.sh SOLAR_ROOT SOLAR_VERIFY OUT [Math|Factory|ERC20|Pair...]
```

Each export is `solar-verify --emit-lean` (manifest version 2) of the spec-applied port. Every
required obligation is accepted only by a kernel-checked proof of `<ob>.Valid` whose axioms are
`propext`, `Classical.choice` and `Quot.sound`: cvc5's refutation rebuilt by lean-smt
(`vc_smt`) first, then `vc_valid`. `OUT/vcs/<C>/discharge/results.tsv` has one row per obligation
and backend with its axioms, `summary.tsv` the verdict per obligation and the vacuity column
(`yes`: the kernel also proves the obligation with goal `false`, so its path is unreachable).
Math.sqrt's loop invariants are solar-verify's inferred ones, re-proved here like any obligation.

Two leaves of `vc_valid` exist for these exports (Verify/Discharge/Leaf.lean): `omega` after
reading SMT-LIB's `div` and `mod` as `/` and `%` (Math's `y / 2`), and `omega` with the facts of
Verify/Discharge/Nonlinear.lean: square bounds, division bounds and the two Newton-step facts of
the integer square root, `y < ((y / x + x) / 2 + 1)²` for `1 ≤ x` (the arithmetic-geometric
mean step, `newton_lt`) and `x ≤ (y / x + x) / 2 → x * x ≤ y` (`newton_le`), each a theorem.
Verify/Discharge/IteApply.lean makes a store into a nested mapping (an ERC20 allowance)
readable by both backends.

## Results so far (2026-11-13, partial: the runs were still going)

With `DISCHARGE_BACKENDS='smt=vc_smt;vc_valid=vc_valid@90'`, 150 s per attempt, on a loaded
machine (`OUT/vcs/<C>/discharge/summary.tsv`):

| Contract | Required | Rows run | Proved (smt / vc_valid) | Failed | Vacuous |
|---|---|---|---|---|---|
| Math | 82 | 40 | 31 (18 / 13) | 9 | 0 |
| ERC20 | 40 | 10 | 8 (8 / 0) | 2 | 0 |
| Factory | 27 | 3 | 1 (1 / 0) | 2 | 0 |

Every proved row's axioms are `propext`, `Classical.choice`, `Quot.sound`. Failures: Math's
`sqrt#46, 49, 52, 53, 56, 57, 58, 65, 69` (cvc5's `div` purification is not reconstructed;
`vc_valid` either exceeds simp's step bound when reading `ediv` as `/` or lacks a nonlinear fact),
ERC20 `transfer#1, #2` (the same reconstruction gap, `vc_valid` timing out), and Factory's
quantified-invariant rows (both backends time out). No row fails by a counterexample.
