# small-contracts: result (2026-11-14)

Lane bundles against the PR heads solidity-lean `9fb89ee` (alpharush/certified-translation) and solar
`38b5232ad` (alpharush/certified); apply with `git fetch <bundle> lane/sc2`.

- `solidity-lean.bundle`: `9fb89ee..6800bb4` (`solidity-lean.commits`)
- `solar.bundle`: `38b5232ad..92e13f428` (`solar.commits`)
- logs (full, every `#print axioms`): `certify-verify_counter.clean.log`, `certify-events.clean.log`
  (the CERTIFIED runs); `*.run1.log` are earlier non-clean runs.

Command (hosted Hand, 5 cores, 14 GB), solar and solar-verify built by the run:

    CERTIFY_CLEAN_BUILD=1 LEAN_MEMORY=6000 LEAN_NUM_THREADS=2 LEAN=<lean wrapper, LEAN_NUM_THREADS=1> \
      SOLIDITY_LEAN_DIR=<sl> SOLC=<solc 0.8.35> SOLAR_VERIFY_Z3=<z3> scripts/certify <sl>/Certified/NAME/NAME.sol

LEAN_MEMORY=6000 is needed for a clean build: with the default 3000 the upstream module
SolidCore/Solidity/Interface/Statements.lean fails (kernel excessive memory).

## Per contract

| contract | status | E3 | E4 | E5 | E6 | E7 | E8 |
|---|---|---|---|---|---|---|---|
| verify_counter | **CERTIFIED**, exit 0, 3284 s, peak child RSS 10094 MB (solidity-lean f962c2a, solar 280c89c) | proved | proved | proved | proved | proved | proved |
| events | **CERTIFIED**, exit 0, 2350 s, peak child RSS 10332 MB (solidity-lean b6d8550, solar 92e13f428) | proved | proved | proved | proved | proved | proved |
| mulx | not certified | proved (generic) | proved | - | - | **missing** | - |
| bank | not certified | proved (generic) | proved | - | - | **missing** | - |
| verify_token | not certified | proved (generic) | proved | - | - | **missing** | - |

Both CERTIFIED runs: check_final axioms [propext, Classical.choice, Quot.sound]; kernel replay ok
(472 and 425 modules); backend negative tests all passed (15, 11); final_neg: every variant refused
(stale byte, substituted artifact, wrong gas bound, wrong post, no allowed status, vacuous specs,
hijacks, sorry). Premises (env): none. Scope: one frame, caller 0x2000.

### verify_counter (source-sourced)

`Certified.verify_counter.Final.final : Certified.verify_counter.Final.Statement`:

    Shapes.Certified (SolidCore.Refinement.Generic.Loop.solidCoreRuntime Source.fuel) c code
      ShapeSource.ValidS ShapeSource.Allowed
      (Shapes.bundlePost Certified.verify_counter.gen.Counter.Spec.Counter ctxOfCall idStep)
      Bump.gasBound

`Source.contract? = .ok c` is SolidCore's checked Counter, its AST bound to this run's source by
source_bind (solc 0.8.35); `code` is byte-equal to this run's solar output; `NonVacuous` is in the
statement. The source is SolidCore, not the MIR-sourced Functional wrapper: E3 is
`StageSource.mir_eq` (generic erasure, the loop's ranking certificate). The postcondition is the spec
solar-verify exported in the run: `Contracts/VerifyCounter/ShapeExport.lean` proves it from
`Source.success_spec` (`published`, `nonvacuous`). Valid: `bump(n)`, `n < 2^32`, no value, any
storage. Remaining caveat (not provenance): solar-verify's SMT VC for bump is refused
(`set-option :timeout 0` is outside the Lean fragment); the statement does not use it.
`Contracts/VerifyCounter/SourceAst.lean` was regenerated from Certified/verify_counter/verify_counter.sol
(same AST body; header in the front end's layout so source_bind accepts it).

### events

`Certified.events.Final.final`: `Shapes.Certified` against SolidCore's checked Events on
`genericValid fns []`, allowed `Shapes.bundleAllowed` and post `Shapes.bundlePost` of the export
(transfer succeeds-if msg.value == 0), gas bound 2386812. Caveat: no separate solidity-lean source theorem
(`headline`), which is not part of the certified statement.

### What blocks the other three (E7)

- **mulx**: the generic tactics do not close m and n. Through `tree_meets_map'` (handles the uint8/uint16
  conditional decode) `m_meets0`/`n_meets0` time out in whnf at 4M heartbeats and hit kernel memory;
  `tree_succeeds` exceeds simp's step limit. The packed narrow products need a hand proof of the tree.
- **bank**: deposit/depositFor read and write `balances[msg.sender]`; the only wired hash premise is the
  global `MapSlotsSeparated [0]`. The footprint-scoped premise (27a02d4, `ScopedSep`/`MapScope`) is not
  yet in a statement: `MapScope`'s `apart` quantifies over every address, so no concrete call shows it
  and it cannot sit in Valid (inhabited); `ScopedSep` can, once the spec's frames are stated over the
  footprint instead of `forall a`.
- **verify_token**: the same premise gap, plus **any sender**: `SolarTV.Call` has no caller field and
  `Target.preState`/`ctxOfCall` fix 0x2000, so no statement can quantify the sender. Needs a caller in
  `Call` (or a sender-indexed Target) from the statement infrastructure.

## Generic pieces in the bundles

- `Verify/ShapeSpecExport.lean`: allowed statuses from the export (`bundleAllowed`), value-guarded
  succeeds-if, `holdsFn_genericValid`, nonvacuous witness helpers.
- `Verify/Spec/TreeSucceeds.lean`: `TreeSucceeds`, `tree_succeeds`, `tree_succeeds_map`, `tree_meets_map'`,
  `mapSlotsSeparated_nil`.
- solar driver: `source_sem`, `allowed_export`, spec_connect for succeeds-if specs, and a fix so
  spec_connect's imports build before its probe (needed for clean builds).
