# refuter-6: what still reaches the strongest status (round 3)

Driver: solar `alpharush/certified` **902cccc2c** (scripts/certify, tools/certify/final.py,
check_final.lean, replay.py). Lean: solidity-lean `alpharush/certified-translation` **f8a4a74**
(transfer `Shapes.Certified` at caller 0x2000). Target: docs/CERTIFICATION_TARGET.md.

## Summary

| id | class | 902cccc2 / f8a4a74 | evidence |
|---|---|---|---|
| R1 | premise equal to the conclusion | **still strongest** | Refute6/out/v3-r1-premise-is-conclusion.out |
| R1b | premise `False` | **still strongest** | v3-r1b-premise-false.out |
| R4 | gas bound 2^64-1 | **still strongest** | v3-r4-gas-2p64.out |
| R4b | committed bounds above the Osaka tx cap | **still strongest** (bank, verify_token) | final.py on committed shapes, below |
| R5 | statement input shadowed by an imported `Certified.<name>` | **still strongest** | v3-r5-shadowed-valid.out |
| R6 | valid calls narrowed to one call | **still strongest** | v3-r6-one-valid-call.out |
| R8 | planted `.lake/build/bin/leanchecker` | **fixed** (absolute path; `no_planted_bins`) | v3-r8-planted-bin.out, v3-r8-skipkernel-control.out: refused by the kernel replay |
| R9 | open_functional with no admitted world | labels "proved", not strongest (kind) | v3-r9-open-empty-worlds.out |
| R10 | planted `.lake/build/lib/libdl.so.2` | **still strongest**, full closure replay | v3-r10-planted-libdl-full.out; control with the fix: refused (v3-r10-fix-control.out) |
| H1 | universal `MapSlotsSeparated [0]` premise | published by bank and verify_token at strongest | below |
| T1-T3 | transfer statement (f8a4a74) | sound for its stated scope; gaps below | below |

"Strongest" means the driver's own rule: final.py's record flag, every status "proved" or "not
applicable", check_final accepting the exact type and axioms, and the kernel replay passing. With a
clean provenance (CERTIFY_CLEAN_BUILD=1, committed inputs), that is when scripts/certify prints
CERTIFIED.

## Method and receipts

Harness `Refute6/variant2.sh LEAN_DIR SOLAR_DIR counter Counter LABEL 'EDIT'` runs step 6b of the
driver with SOLAR_DIR's tools: final.py, `audit.sh scan`, `$toolchain/bin/lean` (absolute path,
under `lake env`, as 902cccc2 does) for Statement/Final and check_final.lean, and
`$toolchain/bin/leanchecker --verbose` under `lake env` for the replay (the variant's modules and
Refute6.*; `REPLAY=full` replays and accounts the whole closure with replay.py, as the driver does).
`Refute6/v3-runs.sh` lists every run with its exact edit. Each output ends with a receipt line
`RECEIPT exit=N peak_rss_mb=M wall_s=S cmd=...` (Refute6/rtime.py, getrusage of the children).

- Build: `LEAN_NUM_THREADS=1 lake -R -KleanMemory=6000 build Refute6.Proof Refute6.Model
  Refute6.Shadow Refute6.SkipKernel Refute6.Axioms counter.gen.Counter.Bytecode
  Contracts.Counter.ShapeExport` on f8a4a74 + Refute6: **exit 0, peak 2905 MB, 105 s**
  (Refute6/out/v3-build.log).
- `#print axioms` (Refute6/Axioms.lean, same build): restrict, raise, published_huge, published_one,
  post_rejects1, nonvacuous_one, published_open, nonvacuous_open, Refute6.KeccakModel: [propext,
  Classical.choice, Quot.sound]; allowed_rejects1: [propext, Quot.sound]. No sorry. Refute6.SkipKernel
  is the deliberately kernel-unchecked module of R8/R10 (`debug.skipKernelTC`), the negative input.
- solar 902cccc2 built from its sources (`cargo build --locked --bin solar`, `-p solar-verify`: exit 0,
  peak 1469 MB); its Counter runtime bytes equal Certified/counter/bytecode.hex; its spec export
  regenerated Certified/counter/gen/Counter/Spec.lean and `lake build counter.gen.Counter.Spec
  Refute6.Proof` exits 0.
- Variant runs: peak RSS 7.8-7.9 GB is `lake env` + lean summed over the run's children
  (ru_maxrss of the largest child); each lean ran with `-M 6000`.
- Counter's Lean inputs (Verify/Shapes.lean, ShapeBundle.lean, Contracts/Counter,
  SolidCore/Refinement/Solar/Counter, Certified/counter) are byte-identical between 9fb89ee and
  f8a4a74; check_final.lean is unchanged since round 1; final.py at 902cccc2 adds allowed_export and
  source_sem only.

Note on R8's first control: a `libdl.so.2` left in `.lake/build/lib` by an earlier run made the
plain kernel-unchecked control pass too. Nothing in the driver looks at that directory; it was
removed and both R8 runs repeated (refused).

## Findings still open

**R1/R1b** (premises). final.py takes any `Prop` in shape.json's `env`; the statement is
`bound ∧ NonVacuous ∧ (env → shape)`. A premise equal to the conclusion (proof `id`) or `False`
(proof `False.elim`) is strongest. Fix: premises from a reviewed allow-list checked by check_final
on the compiled statement (constant name and value hash); state them per call inside a generated
`∃ call, Valid call ∧ Env call` witness so an unsatisfiable premise cannot be proved; refuse a
premise whose value mentions the contract, the source or `code`.

**R4** (gas). `Resources` only asks `G call < 2^64`, and any proved bound lifts to every larger one.
**R4b**: EthLib's `TX_MAX_GAS_LIMIT = 16777216` (EIP-7825, Execution/Evm/Gas/Prices.lean:151) bounds
every Osaka transaction (Proofs/Transactions/Validity.lean:163). 902cccc2's final.py on the committed
shapes of f8a4a74 gives the strongest flag, every status proved, to **bank** (bound 155,937,612) and
**verify_token** (42,697,212), and verify_counter's `gasBoundL cert ((n + 2) * 22)` exceeds the cap
for large n. Above the cap no real transaction reaches the bound, so Resources says nothing on chain
while Equiv admits an inert failure below it. Fix: final.py adds `∀ call, Valid call →
G call + intrinsic call ≤ TX_MAX_GAS_LIMIT` to the statement, else resources "not proved".

**R5** (shadowing). Inputs other than spec_export/allowed_export are still written without
`_root_` inside `namespace Certified.NAME.Final`; an imported
`Certified.SolidCore.Refinement.Solar.Counter.ShapeSpec.cspec.Calls := oneCall` replaces the valid
calls, and the record's statement text still shows the unprefixed name. Fix: prefix every input
identifier with `_root_` (or elaborate inputs before `namespace`), and have check_final refuse any
`Certified.*` constant in the statement other than the module's own.

**R6** (valid calls). `valid` is a free input: one call meets `inhabited` and both NonVacuous
witnesses. Fix: the driver writes Valid from solar's ABI export and the declared storage scope
(`genericValid fns storage`); a narrower scope is recorded below strongest with its reason.

**R10** (loader path). 902cccc2 runs lean and leanchecker by absolute path but still under
`lake env`, whose LD_LIBRARY_PATH lists every package's `.lake/build/lib` (the root's third). The
toolchain binaries need libdl.so.2, libm.so.6, libpthread.so.0, librt.so.1 from the system (only
libc++, libLLVM, libz... ship in its lib/). A `libdl.so.2` there (Refute6/r10/shim.c, built with
shim.map's GLIBC_2.2.5 version node) runs before leanchecker's main, prints `replaying M` for each
argument and exits 0. With it, the full closure replay (423 modules planned, replay.py's account)
passes and a proof of `False` added without the kernel check is strongest
(v3-r10-planted-libdl-full.out). How it gets there in a run: `no_planted_bins` checks `bin` only,
guard_build snapshots `lib/lean` only, and lake elaborates the path dependencies' lakefiles
(vendor/*/lakefile.lean) unsandboxed; appending to vendor/evm-interaction/lakefile.lean an `#eval`
that copies a committed file to `.lake/build/lib/libdl.so.2` plants it on the first `lake env`
(checked; reverted). Fix: solar-refuter6-v3.bundle / patch/0001-fix-certify-run-the-checkers-
without-lake-env-s-load.patch (on 902cccc2c): `tc_run` = `lake env env -u LD_LIBRARY_PATH -u
LD_PRELOAD -u LD_AUDIT` for check_final's closure listing, check_final and the replay. With that
invocation the same plant is refused by the kernel replay (v3-r10-fix-control.out, exit 1). Also
worth doing: fail on any file under `*/.lake/build/lib` outside `lib/lean`, and elaborate lakefiles
in the sandbox.

**R9** (open_functional). `env_ok` and `admit` = `fun _ => False` still give equivalence,
termination and spec "proved" and vacuity "proved non-vacuous"; not strongest (kind). Fix: generated
`(∃ env, EnvOk env) ∧ (∃ W, Admit W)` conjunct; the allowed half of NonVacuous over some admitted
world.

**H1** (universal hash premise). bank and verify_token publish `SolidCore.Spec.MapSlotsSeparated [0]`
= `KeccakSeparated` over all 2^160 keys: injective and every image `≥ 2^128`. For a random-like
256-bit hash, 2^160 keys give about 2^32 expected images below 2^128 and 2^63 expected colliding pairs,
so the premise is false by that heuristic (the kernel cannot decide it: an argument, not a proof).
902cccc2's final.py records both at the strongest status. The target asks for the footprint-scoped
form (`ScopedSep`), which the transfer slice uses. Fix: final.py refuses premises built from the
universal definitions (MapSlotsSeparated, SlotsSeparated, NestedSlotsSeparated, HashInj) at the
strongest status.

## The transfer statement (f8a4a74, Contracts/UniswapV2/ERC20/Certified/Transfer.lean)

`certified : ∃ c, contract? = .ok c ∧ Certified (solidCore fuel) c code ValidIn Allowed TargetPost
(fun _ => 8199112)`. Read against the target; no variant reaches a stronger claim:

- Premise: `ValidIn = Valid deployed ∧ Scope`, `Scope` = `ScopedSep (transferFootprint 1 0x2000 dst)`
  per call, inhabited by `call0` with the premise proved of the real keccak256 by the kernel
  (`scopedSep_transfer_example`). Not vacuous; calls whose two slots collide are outside the statement.
- Gas: 8,199,112, under the tx cap (R4b does not apply).
- Bytes: CtxGas.code is exported by scripts/verify/uniswap_v2_erc20_stages.sh from solar 697fc6864,
  whose compiler sources (crates, Cargo.toml, Cargo.lock) equal 902cccc2c's.

Gaps (labels, not soundness):
- **T1 caller.** Valid fixes the caller to 0x2000 (`SolarTV.Call` has no caller field); the target's
  slice says ANY caller. AnyCaller.lean proves E4∘E5 from any caller but E3 does not yet. The theorem
  is named `certified`; it must not be reported as the slice's CERTIFIED until the caller is
  quantified.
- **T2 allowed statuses.** `Allowed` (success or SafeMath's sub/add errors) has no rejection witness
  in Lean (`nonVacuous_target` covers TargetPost only); the driver's NonVacuous asks for both.
- **T3 binding.** There is no Certified/uv2_erc20/shape.json, so the driver neither states this
  theorem with `bound` against its own compile nor replays and audits it: E6 rests on the export
  script, not the published wrapper.

## Not found

No bypass of check_final's exact type check, the Statement/proof split or the axiom audit other than
through the replay (R10). R8 is closed by 902cccc2.
