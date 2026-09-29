# Spec Hunt performance implementation and validation

Engine baseline: `bfa5669da99463e1077bbff7297214219e114532` (PR #84).
Private harness baseline: `ac64cee`.
Branch in both worktrees: `codex/spec-hunt-performance`.
The live triage checkout and its AWS instance were left untouched.

Implemented:

- Shared immutable checked-contract preparation and named assertion groups in
  six expensive suites. Existing states, fuel, arguments and expectations stay
  intact. `Prepared.call_ownContract` proves the call adapter equal by `rfl`.
- Native witness evaluation from exactly the observable helper's module closure.
  External C libraries are linked statically into the plugin. This avoids the
  pinned EVM dependency's missing `Conform.lean` library root and unnecessary
  native compilation of entire upstream libraries.
- Mechanical Interface split into Foundation, ContractMetadata, Expressions,
  Statements and Contracts. TypeCheck no longer depends on the three lowering
  modules; original declaration names and bodies are preserved.
- Targeted `-O0` for statement-lowering C: 4.9–5.5 s compilation versus 133 s at
  `-O3` and 112 s at `-O1`. LoweringUnify execution moves only from 8.7 to 9.4 s.
- Bounded immutable solc AST cache, successful importer-output cache, optional
  persistent EVM oracle cache with raw evidence and provenance. Tool/source,
  compiler request, measurement settings and environment changes invalidate keys.
- Attested native frontend runner and compiled observable helper, with older
  engines and stale builds falling back to the original paths.
- Native failures retry ordinary Lean within the original remaining timeout.
  An initial 883-case replay exposed one native stack overflow on deep input;
  the retry reproduces the baseline's exact observable for that case. Both logs
  remain available. No verdict is cached.
- Reproducible private-harness benchmark CLI and cache/fallback regression tests.

## Measurements

AWS c7a.8xlarge (32 vCPU, 64 GiB); Lean 4.28.0, solc 0.8.35,
Foundry 1.5.1. External Lean dependencies were already cached. Native dependency
objects were warmed during initial experiments; final rebuild measurements must
be read as development-loop measurements, not a pristine first installation.

| Witness | Baseline | Optimized |
| --- | ---: | ---: |
| LoweringUnify | 1,073 s | 9.4 s |
| ValueTyping | 226 s | 5.2 s |
| AnfCallHoisting | 161 s | 4.1 s |
| EnvLoweringUnify | 155 s | 3.0 s |
| StageDCompletion | 119 s | 3.7 s |
| EvalOrderIntrinsic | 69 s | 3.4 s |

The original full project build passed in 1,451.22 s. The optimized adoption
build passed all 2,326 jobs in **285.32 s**, starting from the baseline project
cache and rebuilding all changed semantic modules and their native objects,
proofs and witnesses. Rebuilding all optimized witnesses/proofs with compiled
semantic modules available passed in **61.71 s**. A no-change `lake build` passed
in **1.11 s**. These have different cache states and **are not a pristine-install
speedup ratio**. The native runner's first build after the adoption build added
1.4 s frontend elaboration, 89 ms C compilation and 929 ms linking (individual
Lake job times, excluding launch/planning overhead).

Replay uses 883 fixed cases, 16 processes, 120 s per process invocation. Input
IDs and hashes are frozen independently of the ongoing triage agent.

| Replay | Wall time | Median case | Baseline differences |
| --- | ---: | ---: | ---: |
| Original baseline | 179.37 s | 3.198 s | — |
| Optimized, empty optional disk cache | 162.69 s | 2.910 s | 0 / 883 |
| Optimized, warm optional disk cache | 156.76 s | 2.796 s | 0 / 883 |
| Optimized, ordinary Lean, warm cache | 168.68 s | 2.996 s | 0 / 883 |

Cold replay recorded 842 EVM oracle misses; warm replay recorded 842 hits with
zero misses. The remaining cases bypass this cache. Both native runs retried
one deep input through ordinary Lean within the original timeout and exactly
reproduced its baseline panic observable. An earlier experimental run without
that fallback differed on this case; its timings are not acceptance results.

Every accepted replay retains these baseline counts: 261 NO_DIVERGENCE,
538 SOUNDNESS_GAP, 47 NEEDS_REVIEW and 37 COVERAGE_GAP. The corpus includes
historical disagreements; optimization preserves those classifications.

## Verification

- Full Lean build: all 2,326 jobs pass; proof statements remain kernel-checked.
- All 883 baseline case IDs/source hashes, verdicts, lanes, eligibility,
  raw EVM measurements, Lean observations/failure stages, coverage classes,
  dedup fingerprints and gate results match in cold, warm and interpreted runs.
- Private harness: **69 tests pass** with engine tools/repros present.
- Engine cache/runtime tests: **11 pass**.
- Full contest suite: **85 checks pass**, including live precompile parity,
  constructors/reverts, events/storage and injected divergence controls.
- A deliberately incorrect `chain3vd` expectation (28 instead of 27) exits 1
  with the named failed assertion. The guard still rejects a wrong result.
- `#print axioms Prepared.call_ownContract` reports only `propext`,
  `Classical.choice` and `Quot.sound`; no `sorryAx` or custom axiom is introduced.
- A mechanical move audit preserves all 28,663 nonblank Interface
  declaration/comment lines, excluding imports, namespace wrappers and the
  replaced module introduction. No declaration body lines were added/removed.
- Local Python harness: 65 pass / 4 unavailable engine-tool checks skipped;
  the pre-existing heartbeat test emits a shutdown warning. Local engine
  performance tests also pass (11).

The measured runs used engine source fingerprint
`7aa9bc789cb28d2b260dd2e179b0c9635250f35b666f37d5cddd9b0044e7762b`
and harness fingerprint
`feb3ae18d8618faeca85c82b7356ace08e9439920aa02a28a1baf99e0ae720f3`.
Final review removed a duplicate import and added a post-run harness fingerprint
check to the benchmark. The final source rebuild passed in **58.11 s**; its
883-case replay passed with zero differences in **155.70 s** (median 2.794 s).
The negative assertion control, all 69 harness tests and all 85 contest checks
passed again. The final engine fingerprint is
`c72b4e699e6e89a80645056d49030ee20652f707b8a34fd12b084b83ac0bbe2b`;
the final harness fingerprint is
`34388b897eb66a667faeceb1df59c8b056dbe0713bc07bbbdbb2317338fbf707`.
These match the local worktrees. See `logs/release-build.log` and
`replay-release/summary.json` for this final run.

Full logs, reports, controls and frozen input hashes live outside Git in
`/Users/dan/.codex/worktrees/spec-hunt-performance/evidence`. Verification ran on
Linux x86-64; this work did not benchmark native compilation on the busy Mac.

See `SPEC_HUNT_PERFORMANCE.md` for usage, cache boundaries, and diagnostic flags.
