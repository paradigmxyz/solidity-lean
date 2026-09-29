# Faster Spec Hunt development

Run `lake build` for the complete proof and witness gate. Witness elaboration
loads a native library compiled from the **same Lean semantic definitions**.
The library contains only the observable helper's transitive module imports;
it does not build unrelated EVMYul or Mathlib library roots. Native object files
and the shared library are incrementally tracked by Lake.
For a diagnostic interpreted build, use `lake -KspecHuntNative=false build`.

The six expensive regression suites prepare their immutable checked contracts
once and retain each original call's fuel, state, arguments and expectation.
Named assertion groups reuse an evaluator and still fail the Lean build on any
false result. Preparation does not run a constructor or share mutable call state.

## Rebuild boundaries

`SolidCore.Solidity.Interface` remains a compatibility import. Its declarations
are divided into `Foundation`, `ContractMetadata`, `Expressions`, `Statements`
and `Contracts`, with original names and definition bodies. `TypeCheck` imports
only `ContractMetadata` and its foundation. Thus a change to typed expression
lowering, statement lowering, or contract assembly does not rebuild TypeCheck.
Mutually recursive blocks stay intact. The giant statement-lowering module
compiles its generated C at `-O0` by default: a measured 5.5 seconds versus 133
seconds at `-O3`, with the prepared LoweringUnify suite taking 9.4 versus 8.7
seconds. Other modules retain Lake's normal release optimization. For throughput
profiling, opt into `lake -KspecHuntLoweringO3=true build`. `Checked` explicitly imports both paths.

## Fast adjudication

```sh
scripts/build_fast_runtime.sh
export CONTEST_CACHE_DIR="$HOME/.cache/spec-hunt"
# Run the normal contest commands or the private replay harness.
python3 -m contest.run_samples
```

The build script compiles `specHuntRunner` and publishes an attestation only if
its source snapshot is unchanged during the successful build. The harness uses
the native binary only when both its source and executable fingerprints match.
Rebuild it after changing semantics. A missing/stale attestation falls back to
ordinary `lake env lean`; `CONTEST_NATIVE=0` also selects that fallback.
A native failure (including stack exhaustion on unusually deep input) retries
through ordinary Lean within the remaining original timeout. The native logs
are retained as `lean.*.native.log`, with `native-fallback.json` recording the
retry. Successful native runs and exhausted timeouts are not retried.
The native host runs Lean's frontend separately for each generated input. It
preserves the source AST, typechecker, execution fuel and per-process isolation.
It still elaborates the generated AST; it is not a new serialized-AST protocol.

The observable helper is precompiled once. Its source must exactly match the
Python harness's helper protocol and its artifact must match the successful
build attestation; otherwise the harness emits the original inline helper.
Older engine checkouts remain supported.

## Cache boundaries

- Repeated solc AST requests reuse fresh decoded copies of immutable JSON.
  Keys include the complete standard-JSON request and native compiler identity.
- Successful importer output is keyed by source path/content, contract,
  namespace, importer implementation and compiler identity.
- Successful EVM reference measurements are keyed by all copied source contents,
  the full generated measurement harness, environment/configuration, execution
  settings and native solc/Forge identities. A Lean-only change can reuse the
  EVM reference, while Lean execution and the verdict always run again.
- Cached EVM hits restore raw evidence and record tool fingerprints and a raw
  evidence checksum in `oracle-cache.json`. Reverts, constructor reverts,
  events, storage and addresses retain their original representations.

Memory caches are bounded. Disk caching is opt-in through `CONTEST_CACHE_DIR`;
keep this trusted directory outside submission-controlled directories. Entries
use atomic replacement and checksums; missing/corrupt/unavailable entries miss.
Compiler/importer failures and unsuccessful Forge runs are not cached. Inputs
containing Solidity imports bypass caching until their external dependency
closure can be represented explicitly. EVM code/gas introspection and assembly
also bypass oracle caching, since they could observe the varying measurement
output path in the test harness's bytecode. Tool wrappers also bypass caching,
since their executable bytes do not identify the compiler they select.

`CONTEST_DISABLE_CACHE=1` bypasses both memory and disk caches. AST/importer
cache keys retain source paths, so relocating a submission may miss those caches;
the EVM oracle excludes only the harness-owned temporary output path. Dependency
packages are assumed immutable at their pinned manifest revisions.

## Reproducible verification

`tests/test_harness_performance.py` exercises mutation isolation, corrupt entries,
disabled/unavailable caches, tool/source/settings changes, constructor and
storage input changes, raw revert/event/storage parity, and stale native builds.
The private harness also provides `scripts/benchmark_spec_hunt.py`: replay a
frozen directory of `.sol` files into a new output directory, then use `--compare`
to compare verdicts and both engine observations. It never submits results.
Build and replay timing evidence is recorded in `PERFORMANCE_LOG.md`.
