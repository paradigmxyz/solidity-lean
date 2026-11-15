# Lane B: Sym.simp in place of the repeated Meta.simp of Wide.Tactic.evalGoal

Status: **partial**. Experimental tactic built and running on the real `run_f` goal; full
statement not yet closed by the Sym path alone. Baseline numbers for `run_f`/`run_set` and the
Sym-with-fallback numbers are recorded in the Measurements section (filled from
`~/eval-receipts.jsonl` / `~/b-scratch/*.out`).

## Files

- `Verify/Eval/B/SymEval.lean`: `wide_symex_sym` / `src_symex_sym` (options: `nofallback`,
  `nobridge`, `noshare`, `withdecide`, `debug`, `budget60`). Prints a counters record and
  per-simproc time.
- `Verify/Eval/B/W1Pilot.lean`, `W4Pilot.lean`: `run_f` / `run_set` statements copied verbatim,
  proved with the repository text (`*_base`) and with `wide_symex_sym` (`*_sym`), plus
  `#proof_stats`, `#kernel_recheck`, `#print axioms`.
- `Verify/Eval/B/W1Base.lean`, `W4Base.lean`: baseline-only copies (so a slow Sym run cannot
  hide the baseline numbers).
- `Verify/Eval/B/Explore.lean`: exploration harness (`nofallback debug`), prints the goal Sym
  leaves.

## Design (what is kept, what changes)

Outer structure unchanged: evaluate to a fixed point, split on the innermost closed `if`
condition or the first `match`, close contradictory branches by `omega`, depth 16.

1. **One SymM session per tactic call.** `Sym.SymM.run` is used once only to capture
   `(Sym.Context, Sym.State)`; every later step runs `(x ctx).run st` and stores the new state, so
   the hash-consing table, `inferType`/congruence caches survive rounds, splits and siblings.
2. **Persistent simp cache.** The lower-level API is `Sym.Simp.SimpM.run x methods config state`,
   which takes and returns `Sym.Simp.State` (it resets only `transientCache`/`numSteps`). The
   convenience `Sym.simp` / `Sym.simpGoal` call `SimpM.run'` with a fresh state. The built-in
   `sym => simp` (Elab/Tactic/Grind/Sym.lean) and vcgen (VCGen/Util.lean) also thread it, keyed by
   (variant, extra theorems).
3. **No growing theorem set.** Instead of re-collecting `unfoldableIn` and rebuilding a simp set,
   the `post` simproc unfolds an application whose head passes the *same gate* (`unfoldable`,
   `monadHelpers`, `isMonadInstance`, user-named definitions), using that constant's own
   equation theorems (`Lean.Meta.Tactic.Cbv.getEqnTheorems`, cached per constant in an env
   extension), falling back to the unfold equation only for non-recursive definitions. The rules
   applicable to a term are a function of its head constant, so the persistent cache never goes
   stale when a new definition appears. The only theorem-set change left is the library bridge
   (below), which only ever *adds* rules discovered at the term being rewritten.
4. **Hypotheses**: per-goal `Theorems` from Prop hypotheses (`mkTheoremFromExpr`). The cache
   records the hypothesis set it was built under. On a change, entries whose key or result
   contains (by pointer) the left-hand side of an added/removed hypothesis, or whose proof
   mentions a removed hypothesis fvar, are dropped; a hypothesis with pattern variables forces a
   full reset. Soundness never depends on this (cached proofs are proofs; a stale `.rfl` only
   loses rewriting); it matters for completeness and for not leaking a proof term that mentions a
   sibling's fvar (that would be ill-scoped, caught by the kernel, not unsound).
   **Bug found and fixed:** splitting with `by_cases hpath : $(exprToSyntax c)` re-elaborates the
   condition, so the new hypothesis is not pointer-equal to the goal's condition and the
   invalidation missed it (the sibling then reused the parent's cached `.rfl` for `c` and split
   16 times without progress: counters goals=17, splits=16, omegaClosed=16, symProgressRounds=1).
   Fixed by `MVarId.byCases c` on the exact expression.
5. **Control flow** in `pre`: `simpControl` for `ite`/`dite`/`cond`, `Cbv.tryMatcher` for
   matchers, marked `done` when stuck so branches/alternatives are never entered (entering them
   with unfold-equation fallback unfolds recursive calls forever).
6. **Library simp set bridge**: Meta's default `@[simp]` discrimination tree proposes candidates
   at the current term; each candidate decl is converted once with `mkTheoremFromDecl` and added.
   On `run_f`: 46-66 lemmas converted, 0 conversion failures, 24-39 bridge rewrites.
7. **Fallback**: after Sym rounds, an exact copy of `Wide.evalGoal`'s Meta.simp loop runs on the
   result; progressing rounds are counted (`fallbackRounds`), so 0 means full Sym coverage.

## Where Sym.simp is not a drop-in for this evaluator (concrete, observed on run_f)

- **No zeta.** `have context := …; match … if context.value % W = 0` stays stuck: Sym keeps
  `let`/`have` (simpLet/toBetaApp) and a condition on a let-bound variable never reduces.
  Meta.simp has `zeta := true`. Added a zeta simproc (`zetaRw` 1-4 on run_f).
- **No projection-of-constructor reduction.** `State.storage { storage := s, … }` and class
  projections over unfolded instances (`Monad.toBind (Monad.mk …)`) are not reduced by Sym.simp
  (Meta.simp uses `reduceProj`/dsimp). Added `projStep` (15-54 rewrites on run_f).
- **Kernel projections are fatal.** An unfold equation whose right side contains `Expr.proj`
  under binders (`__discr.1` from `Stmt.eval`'s `eq_def`) makes Sym.simp throw "unexpected
  kernel projection term". `share` does not repair open terms. Added a `pre` fold step and
  restricted the unfold-equation fallback to non-recursive definitions.
- **Reducible definitions and instances cannot be "unfolded" by Sym theorems**
  (`getSimpTheoremNames` rejects reducible defs/projections); instead `shareCommon` eagerly
  unfolds every reducible constant (instances, `abbrev wordCount`) at preprocessing. So
  `isMonadInstance` constants never appear; patterns are preprocessed the same way, and instance
  arguments are compared with `isDefEq` (Pattern.lean), so `interaction_bind` still fires.
- **Matching is syntactic up to reducible unfolding**, not `isDefEq` at instances transparency
  as in Meta.simp. Example: the split condition re-elaborated by `by_cases` vs. the goal's
  condition (above). Equation lemmas of a recursive function applied to a non-constructor or a
  partial application (`Stmt.eval fuel fns ctx rt` mapped over a list) do not fire; Meta.simp
  behaves the same for eqns but its delta for non-recursive defs is broader.
- **Ground arithmetic limits.** `evalGround` has `maxExponent := 255` by default, so
  `x % W < 2 ^ 256` keeps `2 ^ 256` and `mod_word_lt` (stated with the literal) never matches;
  Meta.simp's `Nat.reducePow` reduces it. Using `evalGround {maxExponent := 512}`.
- **decide := true has no Sym counterpart.** Emulated with `whnf (decide p)` at default
  transparency on closed props (`of_decide_eq_true rfl`). On `run_f` this made the run not finish
  in 15 min (killed); off by default now (`withdecide` to enable), with a heartbeat cap. Kernel
  cost of such proofs is the same evaluation again.
- **Non-contextual ite.** `simpIte` simplifies only the condition; branch bodies are left raw until
  the split. Meta.simp simplified branches too, so the goals handed to the split differ in shape
  (the post-split script of `run_f` may need adjusting).
- Sym.simp's cache key is a pointer: any Meta tactic in between (`split`, `by_cases`, `omega`)
  returns unshared terms; `preprocessMVar` re-shares into the *same* table, so pointers of
  unchanged subterms are preserved only because the session (table) is threaded.

## Measurements (all on hand-written pilot statements; none on generated VCs)

Machine: hosted Hand, check.sh slot, LEAN_NUM_THREADS=1, -M 5000, maxHeartbeats 0 (as in the
repository statements, so heartbeats are not reported per proof). Logs in ~/eval-logs/.

| fixture | variant | result | wall (file) | profiler simp | profiler type checking | #kernel_recheck | proof tree / DAG | peak RSS | axioms |
|---|---|---|---|---|---|---|---|---|---|
| run_f | baseline wide_symex (W1Base) | proved | 10.7 s | 5.2 s | 265 ms | 202 ms | 6,483,989 / 36,502 (+16 aux, 1,669) | 2.57 GB | propext, choice, Quot.sound |
| run_set | baseline wide_symex (W4Base) | proved | 33.0 s | 24.6 s | 405 ms | 493 ms | >=10M (cap) / 57,837 (+17 aux, 758) | 2.66 GB | same |
| run_f | wide_symex_sym v1 (Cbv.tryMatcher) + fallback | proved | 27.0 s (both proofs) | 9.8 s | 422 ms | 142 ms | 6,907,891 / 38,348 | 2.61 GB | same |
| run_set | wide_symex_sym v1 + fallback | **not proved** (tail script mismatch, sorry) | 32.1 s | 23.1 s | 733 ms | 119 ms | - / 28,559 | 2.69 GB | sorryAx |
| run_f | wide_symex_sym v2 (discriminants + match eqns only) + fallback | proved | 12.7 s (both proofs) | 10.9 s | 372 ms | 145 ms | 6,791,967 / 37,722 | 2.61 GB | propext, choice, Quot.sound |
| run_set | wide_symex_sym v2 + fallback | proved | 35.2 s (both proofs) | - | - | 476 ms | >=10M / 57,488 | 2.74 GB | same |

Evaluator counters (wide_symex_sym):

| run | Sym rounds (progress) | Sym steps | eqn / unfold / delta / lemma / hyp / bridge / proj / zeta rewrites | cache kept / dropped / final | Sym ms | fallback rounds (goals) | fallback ms |
|---|---|---|---|---|---|---|---|
| run_f v1 | 5 (2), 1 Sym.simp hit the 400k-heartbeat cap in `whnf` | 361 | 156 / 17 / 18 / 62 / 4 / 37 / 90 / 11 | 197 / 23 / 332 | 16,935 | 18 (2) | 5,686 |
| run_set v1 | 2 (1) | 1,103 | 140 / 19 / 18 / 62 / 2 / 33 / 77 / 16 | - / - / 1,065 | 470 | 5 (1) | 564 |
| run_f v2 | 6 (3) | 497 | 22 / 6 / 13 / 8 / 3 / 18 / 32 / 1 | 644 / 23 / 452 | 188 | 18 (3) | 6,846 |
| run_set v2 | 2 (1) | 277 | 12 / 6 / 13 / 8 / 1 / 18 / 30 / 1 | - / - / 259 | 92 | 11 (1) | 27,628 |

Reading: Sym coverage is partial. v1 evaluates much deeper (run_set: 1,103 steps, 140 equation
rewrites, Sym+fallback 1.0 s vs baseline ~24 s of simp) but (a) on run_f `reduceRecMatcher`'s
`whnf` at default transparency on a discriminant built from symbolic call data ran to the
heartbeat cap, and (b) on run_set it leaves the decoded argument as
`List.foldl … (List.take 32 (… Dirty.argBytes [w.toNat])) % W` instead of `w.toNat`:
`readWord_argBytes'` (conditional: `∀ a ∈ args, a < 2^256`, `off % 32 = 0`,
`off / 32 < args.length`) did not fire before `ABI.readWord?` was unfolded, so the repository's
post-evaluation script fails. v2 removes the `whnf` path and is sound and complete on both
statements, but Sym then stops at the outer layers and the Meta fallback does nearly all the
work (no speedup; run_set's fallback alone takes 27.6 s vs baseline 24.6 s). No speedup is
claimed. Kernel recheck times of the Sym variants are within run-to-run noise of the baseline
(181-218 ms run_f base across runs).

## Addendum items

- Experiment (1) persistent parent session with branch-local `Grind.Goal` vs fresh goals: **not
  attempted** in this lane (time lost to runtime restarts). What this lane does deliver is the
  analogous *Sym.Simp* experiment: a persistent `Sym.State`+`Sym.Simp.State` threaded down the
  split tree with per-branch hypothesis scoping and invalidation (`noshare` = fresh cache per
  goal for the comparison).
- Sibling-isolation negative test: **not attempted** as a standalone file. The invalidation drops
  every entry whose proof mentions a removed hypothesis fvar; a leaked entry would be an
  ill-scoped proof and fail the kernel check, so a leak cannot produce a false proof.
- cbv: `Lean.Meta.Tactic.Cbv` is built on Sym.Simp; its public pieces (`getEqnTheorems`,
  `getUnfoldTheorem`, `tryMatcher`, `reduceRecMatcher`, `isBuiltinValue`, `isProofTerm`) are
  what this adapter reuses. Plain `cbv` is wrong for the evaluator: it unfolds every constant
  with a value (including `Nat.add`/`BitVec` ops on free words); this adapter is "cbv gated by
  the interpreter's unfold predicate" (opaque boundaries kept by the gate, not `@[cbv_opaque]`).
- Generated VCs: no module under `Certified/verify_counter` or `Contracts/VerifyCounter` uses
  `wide_symex`/`src_eval`/`src_symex` (grep). The fallback target (sym_eval/seg_eval of
  `W1Proofs.Segment` as used by `Contracts/VerifyCounter/Bump.lean`) is a different evaluator
  (`dsimp only` + `simp only` macros over EVM/MIR steps); **not attempted**.
