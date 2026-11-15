# Lane H: trust gate, mutation tests, cold replay

Goal: nothing another lane produces may weaken what is proved. Lane H adds four checks, all under
Verify/Eval/H and scripts/eval/audit, every Lean run through scripts/eval/check.sh (one slot at a
time). The olean files of H's library modules (Mutation, Expected, Audit, Close) are compiled with
`lake env lean -o` into .lake/build/lib/lean/Verify/Eval/H (no `lake build`).

## 1. Expected statements (Verify/Eval/H/Expected.lean) — delivered

    #same_statement foo_new foo_old            -- types identical (Expr.eqv, universes renamed by position)
    #same_statement foo_new foo_old (defeq)    -- or defeq at reducible transparency only
    #expect_statement foo_new : Stmt           -- the type is exactly the elaborated Stmt
    #same_imports foo_new foo_old              -- the two modules' import sets agree
    #statement_hash foo_new                    -- Expr.hash of the normalized type (manifest key)
    #expect_reject in <command>                -- negative test: passes only if the command errors

Each check fails the file and prints the first differing subterm. Tests
(Verify/Eval/H/ExpectedTest.lean, exit 0, 1.9 s, 1.6 GB peak): the same statement and an
`abbrev` of it pass (the abbrev only with `(defeq)`); rejected: boundary moved
(`x + 2` for `x + 1`), `<` to `≤`, a dropped conjunct, an extra hypothesis, a narrowed
quantifier (Fin 10 for Nat), a weaker statement hidden behind a non-reducible `def` (also with
`(defeq)`), a universe-monomorphic copy of a polymorphic statement; and `#expect_reject` itself
fails when its command passes.

Usage for lanes: next to every new proof of a baseline theorem, add
`#same_statement new old` (and `#same_imports` when they are in different modules).

## 2. Transitive axiom audit (scripts/eval/audit/axioms.sh, Verify/Eval/H/Audit.lean) — delivered

* From source (default: every Verify/Eval/**/*.lean, or `--files`): the file is copied to /tmp with
  `import Verify.Eval.H.Audit` added and `#audit_axioms_here` appended, then checked with check.sh.
* From .olean (`--modules M ...`): `import M; #audit_axioms_module M`.
* One `AXIOMS<TAB>file/module<TAB>decl<TAB>kind<TAB>statement-hash<TAB>axioms` line per theorem
  (`Lean.collectAxioms`, i.e. what `#print axioms` prints). Any axiom outside propext,
  Classical.choice, Quot.sound fails the run (sorryAx, Lean.ofReduceBool/ofReduceNat — native_decide
  and bv_decide's certificate — Lean.trustCompiler, any user axiom). It also fails when a theorem
  mentions a non-core definition with `@[implemented_by]`.
* Source scan (scan_sources.py, comments and strings stripped): native_decide, bv_decide, sorry, admit,
  axiom, ofReduceBool, trustCompiler, implemented_by, @[extern], skipKernelTC, `cbv … at *`, unsafe.
  allow.txt lists the measurement helpers (Common/Measure dagSize, E/Stats dagSizeMany).
* `--selftest`: six bad fixtures (scripts/eval/audit/fixtures/Bad*.lean: native_decide, bv_decide,
  sorry, a user axiom, an axiom built by a macro the scan cannot see, a theorem over an
  implemented_by def) must each fail the Lean audit alone and the full audit: 12/12 rejected.

Findings from building it:
* bv_decide on an easy goal (`x &&& x = x`) closes in its preprocessing and depends on no
  ofReduceBool, so the axiom audit alone would pass it; the source scan still flags it. The fixture
  uses a goal that needs the SAT certificate.
* A first version flagged every `@[extern]` (Nat.decLt, UInt8.toNat) and so rejected
  Verify.CounterBump and Verify.W1; the kernel evaluates those reference definitions, so only
  non-core implemented_by is flagged now.
* `lake env lean` (check.sh) does not pass the lakefile's leanOptions (maxHeartbeats 1000000,
  backward.do.legacy true); `lake build` does. A module can therefore check under lake build and
  fail under check.sh or the other way round (F/ClzOld fails under check.sh: simp step limit).

### Runs (2026-11-15)

* Self-test: 12/12 bad fixtures rejected (~/eval-audit/selftest.log).
* Built modules from .olean (generated end-to-end ones marked *): Verify.Basic 28 theorems,
  Verify.Tactic 0, Verify.CounterBump 11, Verify.W1 257, Verify.W4 376,
  Contracts.VerifyCounter.Inferred* 0, Contracts.VerifyCounter.Bump* 97,
  Contracts.VerifyCounter.BumpTotal* 83: all pass, axioms only propext / Classical.choice /
  Quot.sound (852 rows, ~/eval-audit/modules.tsv).
* Contracts/VerifyCounter/BumpWrongRank.lean* from source: passes the audit (falling_accepted uses
  the three standard axioms) and its two `fail_if_success` hold; with `fail_if_success` removed the
  file fails at the rank leaf (`omega could not prove the goal`, the false `i + 2 < i + 1`), so the
  wrong certificate is rejected by the leaf tactic, not by a timeout.
* Every non-fixture Verify/Eval file from source (B, C, D, E, F, G, H; 4219 rows,
  ~/eval-audit/lanes.tsv, logs /tmp/eval-audit.MVBUEx): no Lean.ofReduceBool, Lean.trustCompiler or
  user axiom anywhere; sorryAx appears only in files that do not check:

| File | Result | Cause |
| --- | --- | --- |
| B/Explore | fail (scan) | `all_goals sorry` (exploration file) |
| B/W4Pilot | fail | type mismatch ~l.65 → run_set_sym has sorryAx |
| C/GenC1, C/Isolation, C/Stepper | fail | git merge-conflict markers (`<<<<<<< f64e9b05`) in the sources |
| C/Probe | fail | omega |
| E/Stats | not checkable alone | imports E.Toy, no .olean (cold replay handles it) |
| F/ClzOld, F/CheckedExpOld | fail | simp step limit / nested error under check.sh options |
| G/Bench | fail | parse error ~l.116 → evalGCompare sorryAx |
| G/Real/BumpLeaves | fail | grind fails on some leaves, g_close_all leaves a goal → leaf*_grind sorryAx |
| G/Cbv/Mulx, G/Capture/AbiHash | not checkable | mulx.gen.*, abi_hash.gen.* not built |
| all others (B 4, C 2, D 5, E 1, F 6, G 10, H 8) | pass | standard axioms only |

The owners of each failing file were sent the details.

## 3. Mutation tests — delivered

Harness (Verify/Eval/H/Mutation.lean):

    #mutation_check "name" : original rejects [ "label" => mutant, ... ] using tac

runs one fixed script on the original (it must close it with no goals, no error, no sorry or
metavariable, and the kernel must accept it; it is then added as theorem `name`, so the audit
sees it) and on every mutant from a restored state (each must be rejected: exception, logged error,
goals left, sorry, or kernel refusal). A surviving mutant fails the file
(`MUTANT SURVIVED`); Mutants/Sibling.lean shows the harness catches an equivalent mutant.

Results (each mutant rejected by the same script that proves the original):

| File | Engine | Checks | Mutants rejected | Wall | Peak RSS |
| --- | --- | --- | --- | --- | --- |
| Mutants/SolM.lean | sc_vcgen cascade (Loom wp simp + sc_close, copied from Verify/Tactic) | branch, inc, inc_revert, transfer | 3+4+2+4 = 13/13 | 5.8 s | 1.95 GB |
| Mutants/StdDo.lean | vcgen (Std.WP) + sc_close | branch, inc, inc_revert | 9/9 | 6.5 s (whole file) | 1.73 GB |
| Mutants/StdDo.lean | vcgen + grind | branch, inc, inc_revert, transfer | 13/13 | (same file) | |
| Mutants/StdDo.lean | mvcgen (Std.Do) + sc_close | branch, inc, inc_revert | 9/9 | (same file) | |
| Mutants/StdDo.lean | mvcgen + grind | transfer | 4/4 | (same file) | |
| Mutants/Evm.lean | EthLib evm_step / evm_stop | PUSH1 PUSH1 ADD STOP | 4/4 | 4.5 s | 2.5 GB |
| Mutants/Sibling.lean | grind per branch, one grind session, simp_all per branch | sibling isolation | 9/9 | 2.3 s | 1.6 GB |

Mutant kinds: wrong branch (spec swapped; model swapped), `<` vs `≤` at the branch boundary,
2^256-1 vs 2^256-2 and `< 2^256` for the checked increment, revert claimed as success (inc at
2^256-1; transfer without `amt ≤ balance`), wrong revert data, wrap claimed mod 2^255, self-transfer
alias (spec without the `src = dst` case; a stale-read transfer that reads both balances before
its two sstores to the same slot, which mints `amt`), slot aliasing modulo 2^256 (src not bounded),
gas exhaustion (8 gas for a 9-gas run, symbolic and exactly 8), wrong gas left, a program whose second
ADD underflows the stack.

Findings:
* `mvcgen` is deprecated in 4.35 (use `vcgen`). On `throw` in `StateT σ (Except ε)` it leaves
  unassigned universe and monad metavariables as goals (`Type ?u → Type ?u`, `PostShape`,
  `Monad ?m`) and the theorem then fails with "contains universe level metavariables"; the models
  revert with `StateT.lift (Except.error _)` for mvcgen. `vcgen` has a spec for `throw` but none
  for `StateT.lift (Except.error _)` ("No spec found").
* mvcgen leaves the post-state as a `let` (`t✝ : Unit × Storage := …`); closers need zetaDelta.
  vcgen leaves `(PUnit.unit, f).snd k` unreduced; closers need `dsimp only`.
* On the transfer VCs of vcgen and mvcgen, sc_close's `simp_all` hits maxRecDepth (the same VCs
  close with grind; the Loom/SolM form closes with sc_close). Those two rows run with grind.
* Sibling isolation: no fact leaked across `x = 0` / `x ≠ 0` siblings, nor through the
  conditional rewrites `f_zero`/`f_succ`, with grind per branch, with one grind session over the
  whole conjunction (internal case split, shared E-graph) or with simp_all per branch.

## 4. Cold replay (scripts/eval/audit/cold_replay.sh) — delivered

Builds /tmp/eval-cold.XXXX: sources linked, Verify/Eval copied (lean resolves its input path, so a
symlink would leave the cold root), the root's built .olean files linked with
`cp -rs` and the copy's Verify/Eval build directory removed (symlinks under /tmp only). The
selected modules and their Verify.Eval imports (Verify.Eval.H.Audit always first) are checked from
source in dependency order with check.sh `-o` into the cold copy, then audited from their cold
.olean; statement hashes and axioms are compared with scripts/eval/audit/manifest.tsv. `--save`
writes the manifest, and refuses to when any check or audit failed. Other lanes write their olean
files into the real .lake/build/lib/lean/Verify/Eval (A, C were doing so during this run), which is
exactly what the cold copy keeps out.

Runs: `--save` then compare on 11 modules (H's 9, Common/Measure, F/Clz): both PASSED,
178 manifest rows, 0 differences (~/eval-audit/cold_save.log, cold_compare.log; about 10 min each,
mostly waiting for a check.sh slot). Negative check of the comparison, on the compare run's rows
against a tampered manifest: a changed statement hash, an added Lean.ofReduceBool, a declaration
missing from the replay are each reported (3 differences, exit 1); a declaration not in the
manifest is reported as new without failing. The first attempts failed for real reasons now fixed:
symlinked sources (lean resolves the input path out of the cold root), the audit module itself not
replayed, and a `--save` that wrote an empty manifest after failures (it now refuses).

## Addendum (cbv / grind / generated VCs)

| Item | Status | Evidence |
| --- | --- | --- |
| (1) transitive axioms of cbv / grind proofs of B, C, G, D | delivered for every file that checks; C's stepper files do not parse (conflict markers) | lanes.tsv: cbv/decide_cbv proofs of G/Cbv/Sat use propext (and Quot.sound) only; VcGrind, Real/*, D/* standard only; no native_decide, bv_decide, ofReduceBool, trustCompiler anywhere in Verify/Eval |
| (2) cbv negatives with G | delivered except the boundary rule | G/Cbv/Sat and G/Cbv/Mulx check, so their fail_if_success negatives (bad hint, flipped byte, under decide / decide +kernel / decide_cbv / cbv) hold; no `cbv ... at *` in any source; the opaque-interpreter-boundary rule is not checked mechanically |
| (3) grind as SMT backend (vc_grind): unknown never sat, runner negatives stay negative | partial | G/VcGrind.lean checks with standard axioms; H did not run the discharge runner (G owns the frozen rows) |
| Sibling isolation, experiment 1 (persistent Grind.Goal, B and C) | delivered for H and C; no B test found | H/Mutants/Sibling.lean rejects all 3 leak mutants under each of 3 scripts; C/Isolation.lean (after the conflict fix) and G/Tests.lean (sibling_isolation*, with a leaky control) pass the re-audit |
| Sibling isolation, experiment 2 (independent leaves, G on exported rows) | not attempted by H | G owns it; G/Real/BumpLeaves currently fails to check |
| Generated VCs (owner's acceptance) | partial | Bump, BumpTotal, Inferred audited from .olean; BumpWrongRank negative confirmed; Certified/verify_counter, Verify/Discharge/frozen, Verify/VC/*, Contracts/Counter/VC/Export not built here |

## Measurements: generated VCs vs handwritten fixtures

Generated end-to-end VCs: axiom audit of Contracts.VerifyCounter.{Inferred, Bump, BumpTotal} (180
theorems, standard axioms only) and the BumpWrongRank negative (rejected at the rank leaf).
Handwritten fixtures: all mutation tests (Mutants/*), ExpectedTest, the audit self-test fixtures.
No timing claims: wall times above are single runs of whole files on a shared machine.

### Re-audit after the lanes' fixes (05:15 UTC)

After the messages above, the owners fixed their files and H re-ran axioms.sh on them (~/eval-audit/reaudit.log, reaudit_mulx.log):

- B/W4Pilot (370 theorems), G/Bench, G/Real/BumpLeaves (64; the leaves grind does not close are now fail_if_success checks), F/ClzOld, F/CheckedExpOld (failed baselines now pinned as fail_if_success / #guard_msgs), E/Stats, G/Tests (sibling isolation, including a deliberately leaky control that must be rejected), C/GenC1 (93), C/Isolation (5), C/Stepper (14): all pass, standard axioms only. The conflict markers are gone. B/Explore was moved out of the repository.
- G/Cbv/Mulx (228 theorems, including the flipped-byte fail_if_success negatives under decide, decide +kernel, decide_cbv and cbv) and G/Capture/AbiHash (46) pass with LEAN_PATH=~/g-build, where G compiled mulx.gen.* and abi_hash.gen.* outside .lake.
- Only C/Probe still fails (omega at line 14; it is a probe file). It is not a proof any lane relies on.
- Across these files: 0 rows with sorryAx, ofReduceBool or trustCompiler.

From lane G, worth recording for anyone adopting Lean.Meta.Sym's grind discharger: if the shared context is already contradictory at internalizeAll, every later Goal.dischargeSymSimp returns .solved with its proof metavariable unassigned. The result fails closed (the declaration has metavariables), but a caller of mkSymSimpDischarger must record the proof of False itself. G's Facts.discharger does this.
