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

## Results (2026-11-13)

With `DISCHARGE_BACKENDS='smt=vc_smt;vc_valid=vc_valid@90'`, every required row run
(`OUT/vcs/<C>/discharge/summary.tsv`):

| Contract | Required | Proved (smt / vc_valid) | Failed | Vacuous |
|---|---|---|---|---|
| Math | 82 | 82 (34 / 48) | 0 | 0 |
| ERC20 | 40 | 33 (17 / 16) | 7 | 0 |
| Factory | 27 | 21 (19 / 2) | 6 | 0 |

Every proved row's axioms are `propext`, `Classical.choice`, `Quot.sound`; no row fails by a
counterexample. `vc_valid` tries `vc_lite` (Verify/Discharge/Lite.lean) before its search: it
reads pointwise array definitions as function equations, opens a negated quantified goal into a
witness, splits on every `if` and calls `omega` with the facts of Nonlinear.lean, which now also
compare `y / x` with `2`, `x`, `x + 1`, `x + 2` and `x + 3` over the atom `x * x`
(`div_cmp`), expand `(a + 1) * (a + 1)` and bound a Newton step from below. That closes all of
Math.sqrt, including solar-verify's inferred loop invariants and the postcondition
`z * z <= y && y < (z + 1) * (z + 1)`. Quantifiers over two to four integers (Factory's
invariants over pairs of addresses) are evaluated as Lean binders (`eval_forall_int2` to `4`).

Still failing: ERC20 `transferFrom#5, #6, #10, #11` (the conditional allowance update in a
nested mapping: `vc_lite`'s `omega` leaf misses the case split, the search times out) and
`permit#2, #4, #8` (simp exceeds the recursion limit on the signature digest terms), Factory
`createPair#4` to `#9`: their goals need an instance of a quantified assertion about an
uninterpreted two-argument symbol (the pair address of `(token0, token1)`), which neither
`omega` nor the search instantiates; `vc_lite`'s `simp_all` alternative also loops there, and its
recursion-limit error, a runtime exception, is not caught by `first`. These rows prove solar-verify's exported obligations only; tying them to the source
semantics and the bytecode is the spec connection's work (Verify/Spec), not this directory's.
