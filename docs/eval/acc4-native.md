# kernel_rfl copy machinery as native code: measured on acc4-flag

One scoped change, chosen from cost centre 2 of [acc4.md](acc4.md): build
`SolidCore.Refinement.Kernel` and `SolidCore.Refinement.KernelRfl` with `precompileModules`, so
`kernel_clone` and `kernel_rfl … using` run compiled instead of in the interpreter. Chosen over
per-PC equations for sym_exec (cost centre 1, larger) because it changes no tactic, proof,
statement or generated file: the elaborator code is the same, only how it runs differs, and the
kernel still checks every copy. Per-PC equations change the proofs `sym_exec` emits and need
their own soundness and statement review, so they stay next in line (see the matrix below).

## Change (proposed integration, not applied on any RC branch)

Append to `lakefile.lean` after `lean_lib SolidCore` ([kernel-native.patch](acc4/kernel-native.patch)):

```lean
lean_lib SolidCoreKernelNative where
  roots := #[`SolidCore.Refinement.Kernel, `SolidCore.Refinement.KernelRfl]
  precompileModules := true
```

Lake assigns the two modules to this library (it is declared after `SolidCore`), compiles them
to one shared library (C compile 1.2 s + 0.5 s, link 62 ms) and loads it into every module that
imports them; the setup files of Lowering, SpecConnect and KernelCopies list it, Shape's does not.
No Lean source changes. The repository already loads a precompiled plugin (EthLib) the same way.

## Results (same generated VCs: records d66e60bf, base 44572c15, one lock, LEAN_NUM_THREADS=1)

Direct elaboration, 3 runs each, medians ([kernel_native_ab.csv](acc4/kernel_native_ab.csv)):

| Module | mode | wall s | interpreter ms | kernel (type checking) ms | peak RSS MiB | olean sha256 |
| --- | --- | --- | --- | --- | --- | --- |
| Lowering | interpreted | 23.3 | 11,300 | 10,100 | 2,929 | 25c5cad39e025c45 |
| Lowering | native | 13.3 | 224 | 9,730 | 2,918 | 25c5cad39e025c45 |
| SpecConnect | interpreted | 23.3 | 15,800 | 4,160 | 2,786 | 4072ed40d267b52a |
| SpecConnect | native | 10.1 | 286 | 4,060 | 2,783 | 4072ed40d267b52a |

Run spreads: wall ±0.5 s, kernel ±0.5 s. The compiled clone code now shows under "elaboration"
(1.1 s and 2.3 s).

Through Lake (`lake -R build flag_4ce5cf9a.SpecConnect` after deleting the five affected oleans):

| | interpreted | native |
| --- | --- | --- |
| KernelCopies | 15 s | 4.0 s |
| Lowering | 23 s | 13 s |
| SpecConnect | 22 s | 9.8 s |
| whole command wall | 75.0 s | 40.0 s |
| olean sha256 Lowering / SpecConnect | 9dee0d55… / 291e2696… | 9dee0d55… / 291e2696… (identical) |

- Proof terms, DAG sizes, declarations and axioms: unchanged, because the oleans are
  byte-identical in both modes (direct and through Lake). Kernel time is unchanged within noise.
- Peak RSS: unchanged (−11 MiB / −3 MiB).
- The other 24 generated modules do not import the clone code; their times are unaffected.
- On the acc4 total (105.9 s single-thread), this removes about 23 s from the generated
  modules, plus about 11 s from KernelCopies in the import closure.

## Size sweep: one `cloneRootSubst` call under fresh prefixes ([sweep_full.csv](acc4/sweep_full.csv), BenchSweep.lean)

| Root | copies | interpreted ms (2 runs) | native ms (2 runs) |
| --- | --- | --- | --- |
| Dirty.fnShapeOk | 0 | 14 / 14 | 10 / 4 |
| Wide.deployedEmpty | 258 | 10,220 / 10,550 | 930 / 967 |
| Abi.deployedStorage | 258 | 10,422 / 10,471 | 928 / 927 |
| Lowering.contract? | 286 | 10,662 / 10,841 | 977 / 1,036 |
| Lowering.shape? | 297 | 10,748 / 10,993 | 1,039 / 1,003 |
| SpecConnect.deploy? | 500 | 10,926 / 11,323 | 1,066 / 1,085 |

The cost is not linear in the copies made: going from 258 to 500 copies adds about 5–8% in both
modes, and the native call is a steady 10–11x faster. Most of each call is a fixed cost that the
copy count does not explain (the interpreted call would otherwise be ~40 ms per copy). That
fixed part is the next target: find what each call walks (likely the environment or the
reachable-constant closure) and reuse it across calls. This also covers SpecConnect's 890 copies
that duplicate Lowering's. No linearity claim beyond these six points.

## Trust

No change to statements, generated files, verification contracts or axiom policy (still
propext, Classical.choice, Quot.sound; oleans identical, so #axioms_within results are too).
No native_decide, bv_decide, ofReduceBool or trusted SMT: the native code is elaborator code
that proposes declarations; the kernel checks every one of them as before.

## Owners and integration

`lakefile.lean` is shared. SolidCore and generic.py paths belong to another writer, so this
branch does not edit them; integrating means appending the lean_lib above on the RC branch, by
that branch's owner, then one `lake build` there. Reproduce with scripts/eval/acc4/{ab.sh,
lake_ab.sh, BenchSweep.lean} on the acc4 bench of [acc4.md](acc4.md).

## Follow-on matrix (status after this change)

| Item | Evidence so far | Next measured step |
| --- | --- | --- |
| Per-PC fetch/decode equations for sym_exec (acc4 #1, 30.4 s) | acc4.md: 772 dsimp steps 14.6 s, 448 simp* 11.4 s | evm1_run, same statement, compare elab/kernel/DAG |
| kernel_rfl fixed per-call cost and cross-module copy reuse | this doc: ~1 s native per call, 890 duplicate copies | profile one native call, reuse closure |
| Kernel-friendly Keccak for selectors (acc4 #3, 6.6 s kernel) | acc4.md | equality proof + time selSig0_eq |
| SymM / Sym.Simp | b.md: Sym rounds + Meta fallback, no speedup on W1 | try on sym_exec's step simp once per-PC equations exist |
| Persistent Grind.Goal, prefixes, internalize, sibling isolation | c.md: 21 vs 161 internalized decls, isolation negatives pass | reuse in sym_exec path splits |
| cbv / simpControl | g.md: cbv 2–18x slower to check than decide +kernel | keep decide; revisit for Keccak only if kernel Keccak stays slow |
| Std / Mathlib / cslib / Loom / EthLib reuse | f.md equivalences; d.md bridge lemmas | land f.md list behind the RC |
| grind coverage | g.md measures grind itself; no coverage is inferred from SMT results | unchanged |
