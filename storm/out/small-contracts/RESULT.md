# small-contracts: result (partial, 2026-11-14)

Lane bundles against the PR heads: solidity-lean `9fb89ee` (alpharush/certified-translation) and
solar `38b5232ad` (alpharush/certified). Apply with `git fetch <bundle> lane/sc2`.

- `solidity-lean.bundle`: `9fb89ee..f962c2a` (`solidity-lean.commits`)
- `solar.bundle`: `38b5232ad..280c89c` (`solar.commits`); `tools/certify/solidity-lean.rev` pins f962c2a
- `certify-verify_counter.run1.log`, `certify-events.run1.log`: full driver logs, every `#print axioms`

Driver command (hosted Hand, 5 cores, 14 GB):

    SOLIDITY_LEAN_DIR=<sl> SOLC=<solc 0.8.35> SOLAR_VERIFY_Z3=<z3> LEAN_NUM_THREADS=3 \
      LEAN=<wrapper: lean with LEAN_NUM_THREADS=1> scripts/certify <sl>/Certified/NAME/NAME.sol

Each module builds with lean -M 3000 (driver default); the driver builds solar and solar-verify itself.

## Per contract

| contract | driver | E3 | E4 | E5 | E6 | E7 | E8 | CERTIFIED |
|---|---|---|---|---|---|---|---|---|
| verify_counter | CHECKED, exit 0, 2375 s, peak child RSS 11405 MB | proved | proved | proved | proved | proved (export-bound) | proved | only provenance missing (non-clean build); clean-build run in progress |
| events | CHECKED, exit 0, 1621 s, peak 10894 MB (run at a1c3143 + lane, before the rebase) | proved | proved | proved | proved | proved (export-bound) | proved | only provenance missing (prebuilt solar, non-clean build, uncommitted manifests then); rerun pending |
| mulx | not run | proved (generic) | proved | driver | driver | **missing**: spec_connect tactics fail on uint8/uint16 decode and packed products | driver | no |
| bank | not run | proved (generic) | proved | driver | driver | **missing**: deposit's spec needs a mapping-slot premise; only the global `MapSlotsSeparated [0]` is wired, not a footprint-scoped one | driver | no |
| verify_token | not run | proved (generic) | proved | driver | driver | **missing**: (a) any sender: `SolarTV.Call` has no caller and `Target.preState` fixes 0x2000, so no statement quantifies the sender; (b) scoped premise: `HashScope`/`MapScope` (27a02d4) needs `apart` over all addresses, which no concrete call can show, so it cannot sit in Valid (inhabited); `ScopedSep` fits only once the spec's frame is over the footprint | driver | no |

### verify_counter (source-sourced shape)

`Certified.verify_counter.Final.final : Certified.verify_counter.Final.Statement`; check_final axioms
[propext, Classical.choice, Quot.sound]; kernel replay of 472 modules; every final negative refused
(stale byte, substituted artifact, wrong gas bound, wrong post, no allowed status, vacuous specs, hijacks,
sorry); backend negative tests 15/15. Statement:

    Shapes.Certified (SolidCore.Refinement.Generic.Loop.solidCoreRuntime Source.fuel) c code
      ShapeSource.ValidS ShapeSource.Allowed
      (Shapes.bundlePost Certified.verify_counter.gen.Counter.Spec.Counter ctxOfCall idStep)
      Bump.gasBound

with `Source.contract? = .ok c` (SolidCore's checked Counter, its AST bound to this run's source by
source_bind with solc 0.8.35), `code` byte-equal to this run's solar output, `NonVacuous` in the
statement. The source is SolidCore, not the MIR-sourced Functional wrapper: E3 is
`StageSource.mir_eq` (generic erasure, the loop's ranking certificate). The postcondition is the
spec solar-verify exported in the run, not the Lean restatement: `Contracts/VerifyCounter/ShapeExport.lean`
proves `meets` of it from `Source.success_spec` (`published`, `nonvacuous`: axioms
[propext, Classical.choice, Quot.sound]). Premises: none (env []). Scope: `bump(n)`, `n < 2^32`,
no value, any storage; caller 0x2000 fixed. solar-verify's SMT VC for bump is refused
(`set-option :timeout 0` is outside the Lean fragment): a caveat of the SMT path, not of the statement.

### Generic pieces (in the bundles)

- `Verify/ShapeSpecExport.lean`: allowed statuses read off the export (`bundleAllowed`), value-guarded
  succeeds-if, `holdsFn_genericValid`, nonvacuous witness helpers.
- `Verify/Spec/TreeSucceeds.lean`: `TreeSucceeds`, `tree_succeeds`, `tree_succeeds_map`,
  `tree_meets_map'`, `mapSlotsSeparated_nil`.
- solar driver: `source_sem`, `allowed_export`, spec_connect for succeeds-if specs.
