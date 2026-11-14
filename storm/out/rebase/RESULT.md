# rebase lane: alpharush/certified merged with feat/lean-solar

## Deliverable

`solar-certified-merge.bundle` (solar). Prerequisites: alpharush/certified 38b5232ad and
feat/lean-solar 807d57fac (its head on 2026-11-14). It holds branch
`rebase/certified-on-lean-solar` = 79f56213f:

- c1643e46f `chore: merge feat/lean-solar into alpharush/certified`, parents 38b5232ad (first)
  and 807d57fac (second).
- 79f56213f `test(certify): keep the refused export outside the fragment` (a test fix for a
  failure already present on 38b5232ad, see below).

```sh
git fetch origin alpharush/certified feat/lean-solar
git fetch storm/out/rebase/solar-certified-merge.bundle rebase/certified-on-lean-solar:rebase/certified-on-lean-solar
git log --format='%h %p %s' -2 rebase/certified-on-lean-solar
```

The pin `tools/certify/solidity-lean.rev` is unchanged (7aedd63, as on 38b5232ad). Nothing was
pushed to any solar branch.

## Why the merge carries more than feat/lean-solar

feat/lean-solar's merge base with main is e2da3e7; alpharush/certified already contains main
through 05d39ec29 (29 commits more). So lean-solar's files meet main's changes for the first time
here, chiefly #2515 (one `extcall` primitive replacing `AddressCall` and the
`Sha256/Ripemd160/EcRecover/Send/Transfer` builtins), which lean-solar's translation-validation
model was written against. The merge ports that model to `extcall` (see "Semantic port" below).

## Conflicts (46 files) and their resolution

Rule: feat/lean-solar is authoritative for its own files; alpharush/certified additions are kept
on top; where main (via alpharush/certified) removed or renamed an API lean-solar uses, lean-solar's
code is ported to main's API.

| File | Resolution |
|---|---|
| Cargo.lock | alpharush/certified's (a superset: solar-smt, solar-verify deps); `cargo build --locked` passes |
| crates/codegen/Cargo.toml, src/lib.rs | keep certified's `solar-smt` dep and `lean_stages` module |
| crates/codegen/src/backend/evm/ir/passes/mod.rs | keep certified's `lean_stages::evm_pass` hook and `-Zvalidate-evm-ir-passes` query writer around lean-solar's `solar_tv::EvmSnapshot` check |
| crates/codegen/isle/mir/prelude.isle | lean-solar's `AbiWordValidator` type + main's `CallPolicy` (AddressCallKind is gone) |
| crates/codegen/src/target.rs | certified's `Assume` = zero cost + lean-solar's `ValidateAbi { .. }` struct form |
| crates/evmir/src/ir/verify.rs | lean-solar's `stack_entry_exact_depths` (with `forget_exact_depths`); certified's older version and its now-unused helpers `entry_root`/`exact_edges` dropped; main's removal of stack upper bounds kept |
| crates/mir/src/analysis/validator.rs, builder.rs, op_schema.rs, semantics.rs (imports) | union of both sides' imports with `AddressCallKind` replaced by `CallPolicy`/`ExtCallKind`/`CallOutput`, plus lean-solar's `AbiWordValidator`, certified's `AssumePredicate`/`FactSource` |
| crates/mir/src/op_schema.rs (`ExtCall`) | main's `ExtCall { policy, address, input: Option, gas, value }` with lean-solar's `#[semantics(...)]` attribute, now `extcall(policy, ...)` |
| crates/mir/src/semantics.rs, semantics.snap | `Semantics::AddressCall` becomes `Semantics::ExtCall(opcode, CallOutput, address, Option<input>, gas, value)`; snapshot line `extcall: extcall(policy, address, input, gas, value)` |
| crates/mir/src/module.rs | duplicate `function_text` (both sides added one) collapsed to one |
| crates/mir-interpreter/src/{lib,machine,replay,values}.rs | lean-solar's interpreter + certified's `assume`/`Undefined`/`check_integer_widths`; `semantic_address_call` → `semantic_extcall` (see port); `machine/precompiles.rs` and the Send/Transfer arm removed (those builtins no longer exist) |
| tools/solar-tv-replay/src/{main,mir_model,world,world/mir,world/mir/messages}.rs | lean-solar's; keep certified's `assume` export ahead of lean-solar's deferred-allocation marking; `ExtCall` export replaces address_call/precompile_builtin/value_transfer |
| solar-tv/validator/*.py | lean-solar's; keep certified's `assume` import (`.assume .pred`), `Fact.holds` unfold, `lean_root()`; new `extcall` import case |
| solar-tv/validator/common.py `lean_root` | `SOLAR_TV_LEAN` when set, else solar-tv's own package (lean-solar's SolarTV Lean stays in solar-tv) |
| solar-tv/{README,OPERATIONS}.md, operations.json | lean-solar's text/counts; certified's `assume` paragraph and `"assume": "direct_state"` entry kept; `address_call` → `extcall` |
| solar-tv/examples/mir/*/after.mir, tests/*.py | lean-solar's; certified's assume tests kept; tests and examples moved to `extcall` syntax |

### Semantic port to `extcall` (beyond textual conflicts)

- Rust interpreter `semantic_extcall`: input absent / memory object / slice; `word` output writes
  scratch 0..32 (zeroed first unless the callee is constant 2 or 3, matching
  `Function::extcall_clears_word`); explicit gas is the sufficient-caller-gas boundary; implicit gas
  takes the next `builtin_gas` budget (previously unsupported); static on a target without
  STATICCALL is a zero-value CALL, as lowering emits.
- Lean (solar-tv/SolarTV/MIR/State): `MessageOp.extcall opcode hasValue hasInput hasGas word clears`
  with the same rules; `Fact`, `Operation.assume`, `Completion.undefined` and the
  undefined-source refinement in `Observe.equivalent`, matching solidity-lean's tv/SolarTV.
- Tests that used `icall sha256<>`, `send<>`, `transfer<>`, `address_call` now use the frontend's
  emitted shape (`extcall static word i160 N` + `revert_returndata` branch + `mload 0`).

### Pre-existing failure fixed separately (79f56213f)

`tools/certify/test.sh` case spec-refused failed on 38b5232ad alone: since 44260efa0 solar-verify
exports two-dimensional arrays (`.arr2`), so `uint256[][]` is no longer refused. The case now uses
`uint256[][][]` (refused: `C.f: undeclared symbol`). CI's driver-test step runs without
SOLAR_VERIFY and skips this case, so CI did not see it.

## Checks (receipts: command, exit, wall, peak RSS of the largest child)

| step | exit | wall | peak RSS | command |
|---|---|---|---|---|
| certify-counter | 1 | 405s | 4407MiB | `env SOLC=~/bin/solc-0.8.35 SOLIDITY_LEAN_DIR=~/sl SOLAR_VERIFY=~/rb2/target/debug/solar-verify scripts/certify tools/certify/examples/counter.sol` |
| certify-tests | 1 | 7s | 464MiB | `env SOLAR=~/rb2/target/debug/solar SOLAR_VERIFY=~/rb2/target/debug/solar-verify bash tools/certify/test.sh` |
| certify-tests-fixed | 0 | 18s | 465MiB | `bash tools/certify/test.sh` |
| sl-ethlib-prebuild | 0 | 74s | 827MiB | `lake build EthLib.Execution.Proofs.Evm.Logic.Call EthLib.Execution.Proofs.Evm.Logic.Copy EthLib.Execution.Proofs.Evm.Logic.Known EthLib.Execution.Proofs.Evm.Logic.LessGas EthLib.Execution.Proofs.Evm.Logic.Message EthLib.Execution.Proofs.Evm.Machine.JumpDest` |
| cargo-check | 0 | 108s | 923MiB | `nice cargo check --locked --workspace --all-targets` |
| solar-tv-lake | 0 | 20s | 1593MiB | `bash -c 'cd solar-tv && lake build'` |
| nextest-tv | 0 | 34s | 425MiB | `nice cargo nextest run --locked -p solar-tv-replay -p solar-mir-interpreter -p solar-evmir-interpreter -p solar-evmir -p solar-mir` |
| certify-counter-2 | 1 | 676s | 4409MiB | `env SOLC=~/bin/solc-0.8.35 SOLIDITY_LEAN_DIR=~/sl SOLAR_VERIFY=~/rb2/target/debug/solar-verify scripts/certify tools/certify/examples/counter.sol` |
| certify-counter-4 | 0 | 2924s | 7839MiB | `env SOLC=~/bin/solc-0.8.35 SOLIDITY_LEAN_DIR=~/sl SOLAR_VERIFY=~/rb2/target/debug/solar-verify scripts/certify ~/sl/Certified/counter/counter.sol` |
| solar-tv-py | running | | | `python -m unittest discover -s solar-tv/tests` (result in the next delivery) |

Everything ran at 79f56213f (the merge c1643e46f has the same compiler sources). certify-counter, certify-counter-2 and certify-tests are the failed attempts explained below; certify-tests-fixed ran on 79f56213f. nextest-tv: `cargo nextest run -p solar-tv-replay -p solar-mir-interpreter -p solar-evmir-interpreter -p solar-evmir -p solar-mir`.


Toolchain: Lean 4.35.0 (solar-tv's lean-toolchain moved from 4.34.1 to 4.35.0, matching
scripts/evm-rules/lean and .github/scripts/install_lean.sh on alpharush/certified), solc 0.8.35
for source_bind, LEAN_NUM_THREADS=1.

### Counter certify (as CI runs it)

```sh
SOLC=solc-0.8.35 SOLIDITY_LEAN_DIR=<solidity-lean at 7aedd63> SOLAR_VERIFY=target/debug/solar-verify \
  scripts/certify <solidity-lean>/Certified/counter/counter.sol      # exit 0, 2924 s, peak RSS 7839 MiB
```

- Stages stage0 → sched → evm1..evm5 → bytecode built and audited: 23 theorems, axioms only
  propext, Classical.choice, Quot.sound (several only propext, Quot.sound).
- Headline modules built and audited: Counter.Headline.spec_holds_of_bytecode, wrong_fails,
  EndToEnd.inc_spec_bytecode, get_spec_bytecode, Deploy.initcode_runs: [propext, Classical.choice,
  Quot.sound].
- Published statement: `check_final: Certified.counter.Final.final : Certified.counter.Final.Statement
  (module counter.Statement, which does not import Contracts.Counter.ShapeExport); axioms [propext,
  Classical.choice, Quot.sound]`; kernel replay of 422 modules.
- Statuses: equivalence, termination, spec, resources all "proved (published statement)"; vacuity
  "proved non-vacuous"; **strongest False**, line `CHECKED counter`, not `CERTIFIED`. The only
  reason is the provenance caveat "the starting build directory is trusted, not rebuilt from source
  (CERTIFY_CLEAN_BUILD=1)". Assembly: executed inside the published statement; Proofs/Assembly is
  decoded only.
- Negatives, all refused by execution or the kernel/checker (none by timeout): bytecode opcode and
  lt edits; Evm5 add→sub, sstore key, no callvalue check, no overflow check; sched add→sub;
  stale-byte, substituted-artifact, wrong-gas-bound, wrong-post, no-allowed-status, vacuous-spec
  (×3), vacuous-proof (×2), hijack-names/alias/macro/skip-kernel, sorry-proof. Controls accepted.
- Bytecode (runtime, -Ogas --evm-version osaka) is byte-identical to the one 38b5232ad's solar
  emitted in this lane earlier (sha256 daed21b0…f6ec).

Earlier failed attempts, kept for the record: certify-counter (cold EthLib build in the sandbox:
read-only file system), certify-counter-2 (ran on solar's tools/certify/examples/counter.sol, which
has no spec: NonVacuous mismatch; see notes).

## Notes for the integrator

- CI's `solar-tv` job: both sides defined one; the merged ci.yml keeps lean-solar's job (builds
  solar-tv's own Lean) and adds certified's `lean_agreement` step against the pinned
  solidity-lean checkout (SOLAR_TV_LEAN set for that step only); timeout 90 min.
- `scripts/certify tools/certify/examples/counter.sol` (as the README shows) uses solar's copy of
  counter.sol, which has no `@custom:ensures`; the fresh spec export is then empty and
  counter.Final fails (NonVacuous expects inc's spec). CI certifies solidity-lean's
  `Certified/counter/counter.sol`, which has it; that is the run reported above. The example file
  should gain the annotation or the README should point at the solidity-lean copy.
- A cold solidity-lean checkout fails step 6b with "read-only file system" when the proof imports
  EthLib modules not built yet (the sandbox may not write packages). Prebuilding
  `EthLib.Execution.Proofs.Evm.Logic.{Call,Copy,Known,LessGas,Message}` and
  `EthLib.Execution.Proofs.Evm.Machine.JumpDest` outside the sandbox fixed it here; those modules
  are still replayed by leanchecker in the run.
- Not done in this lane: moving the pin to solidity-lean 9fb89ee (alpharush/certified-translation
  head). The merge keeps 38b5232's pin 7aedd63, the commit 38b5232's driver was written for.

