# Release candidate 2026-11-15 (solidity-lean)

Status: **ASSEMBLING, not yet a release candidate.** There is no exact-pin positive at the RC
driver pin yet (see Receipts). The acceptance reviewer, the only publisher of RC artifacts,
updates this file in place, one commit per update on `alpharush/rc-2026-11-15`.

What this candidate claims, if accepted: for contracts inside the supported subset below, the
generic driver produces, with no hand-written proof, one kernel-checked theorem of a fixed shape
(`SolidCore.Verify.Generic.Expected`) about the exact runtime bytes the pinned compiler emitted in
that run. It makes **no claim about Solidity in general**, about init code or deployment, or about
callers other than the fixed one.

## Pins

| What | Pin |
|---|---|
| RC driver (solar) | `alpharush/t1-driver-on-2637b` @ 800d78a98b9e64612c742d5038e7e2ec35dd52b4 (tree eff1b722; parent 1844041e, then c09510a3, on 6cba89f; 1844041e and 800d78a9 change only `tools/certify/generic.py` and `tools/certify/test_generic.py`) |
| solidity-lean base | 44572c150176365fa5e0d56ae6c59a7a443f8122 (`tools/certify/solidity-lean.rev` at the driver pin names it) |
| Lean toolchain | `leanprover/lean4:v4.35.0` (recorded digest 953aa1e7…4c25 in acc4-flag) |
| solc (AST front end) | sha256 fa8ac9a3…17f4 (as recorded in acc4-flag) |
| Held-out set | `alpharush/rc-heldout` @ e0564a28100931a9986af9a848a57bc2bd835c67, copied here under `tests/heldout/rc-2026-11-15/` |

A record certifies at the RC pin only when its run **and** its fresh-clone replay used the RC
driver sha, with all 18 replay pins equal (**exact-pin**). A replay of a record made on another
driver sha is a **compatibility check** only, and exact-pin certification of that record stays
OPEN. Runs started on 1844041e before the pin moved are labelled with that sha and are not RC-pin
records.

## Support matrix (generic driver at 800d78a9, base 44572c15)

Source of truth: `envelope()` in `tools/certify/generic.py` and `docs/SUPPORTED_ENVELOPE.md`.
"Certified instance" means a published record accepted below; none exists yet at the RC pin.

| Feature | Status at the RC pin | Certified instance |
|---|---|---|
| one concrete contract, no bases, no imports | supported | acc4-flag (driver 6d0f2621 only) |
| value-type storage scalars (uint/int/bool/address) | supported | acc4-flag (6d0f2621 only) |
| return values, view/pure functions | supported | none yet (held-out H1, H2 pending) |
| checked arithmetic (Panic 0x11) | supported | none yet (H2 pending) |
| `mapping(K => V)` of value types | supported with premise (Keccak-256 separation over each call's footprint) | none yet (H3 pending) |
| state-variable initializers / constructor without parameters | runtime tier only: the storage is any storage that lists every slot the constructor writes (`Generic.Covers`: those slots, any values); the constructor's run is not part of the claim | none yet (H2 pending) |
| constructor with parameters | BLOCKED (envelope) | - |
| deployment / init code / lifecycle | BLOCKED: no lifecycle or constructor tier at the pin (`--tier` offers compiled, functional, certified) | - |
| caller other than 0x2000 (any-caller) | OPEN: `Context.default` only | - |
| loops (for/while/do) | BLOCKED at the pin in the generic driver; the loop lane's results are not part of this RC until accepted here | - |
| gas / resource certification of loops | BLOCKED: no gas obligation or fuel-bound interface for loops | - |
| external calls, try/catch, `new`, inline assembly, payable, inheritance, imports, several contracts | BLOCKED (envelope) | - |
| Pair | BLOCKED | - |

## Theorem scope

The published theorem of a record named `<n>` is `Certified.<n>.Final.final :
Certified.<n>.Final.Statement`, where `Statement` (module `<n>.Statement`, which does not import the
proof) is

```
code.data.toList.map (·.toNat) = runtimeBytes ∧ Generic.Expected src spec runtimeBytes
```

with `runtimeBytes` the bytes the pinned solar emitted in that run and `src` the solc AST of the
source as SolidCore's checked contract. `Expected` (`Verify/Generic/Expected.lean` at the base) says:
the bytes are bytes; `spec.Covered` holds (some context, every entry has a valid call, the
postcondition and the allowed statuses each reject something: non-vacuity); and, under
`spec.assumptions` (empty for every record here: the unconditional runtime tier), in every covered
context the source type-checks and `CertifiedAt` holds: equivalence at every gas below 2^256 (a
bytecode result is the source's, or a failure that changes nothing), termination, resources (from
the gas bound on, exactly the source's result) and the spec's proof over the same source semantics.

The claims are kept separate:

- **Translation** (the bytes behave as the source): equivalence, termination and resources, for
  valid calls only: ABI-encoded calls of the declared functions with clean argument words, any
  value below 2^256, one frame, caller 0x2000, contract at 0x1000, a fixed block and transaction.
- **Source property** (the source meets its spec): only what the NatSpec `@custom:ensures` and
  `@custom:succeeds-if` say, as solar-verify exported them in that run. No frame beyond what the
  spec states.
- **Lifecycle / constructor**: BLOCKED. Not proved for any record.
- **Resources**: the gas bound is the loop checker's and coarse; below it the bytes may fail
  without effects, which equivalence admits.

## Trusted computing base

- The Lean 4 kernel (v4.35.0) and `leanchecker`'s replay of every module in the closure; each final
  theorem's axioms must be exactly `propext, Classical.choice, Quot.sound`.
- SolidCore's semantics of Solidity source (the solc AST through
  `scripts/solc_ast_to_lean_source.py` and the type checker) is what the source means.
- The EVM model `Final.Target.runWithFrom` in solidity-lean.
- solar-verify's NatSpec export is what "the spec" means.
- The driver scripts at the pin: they decide what is in the envelope, generate `Statement` (its
  shape is fixed; its `src`, `spec` and `runtimeBytes` bindings come from the front end,
  solar-verify's export and the run's compiler output) and check that `final`'s type is exactly
  `Statement`. The reviewer reads each record's generated `Statement.lean` against this.
- Nothing is trusted by directory: every closure here must report `0 trusted`.

## Known blockers and open items

- Pair: BLOCKED.
- Constructor / deployment / lifecycle: BLOCKED (no tier at the pin).
- Any-caller: OPEN (fixed caller only).
- Loops: OPEN at the pin. Gas and resource certification for loops is BLOCKED (no gas obligation or
  fuel-bound interface).
- **Nonvacuity is a separate required check.** solar-verify alone accepts a spec with a
  contradictory precondition unless the separate nonvacuity witness is required. Any loop or spec
  claim in this RC must carry its nonvacuity witness as its own check; a proof without it is not
  accepted. For generic-driver records the witness is `spec.Covered` inside `Generic.Expected`
  (some covered context, and the postcondition and allowed statuses each reject something), and
  the record's in-run vacuity negatives must be refused.
- **Archive integrity**: an edit to an archived `inputs/*` file with its `run_files` entry rehashed
  replayed CERTIFIED (exit 0) at 1844041e. 800d78a9 binds archived inputs to `inputs_sha256` and
  compares caveats with the fresh run; the producing lane reports the input-rehashed,
  shape-rehashed and caveats-forged cases REJECTED with an unedited control CERTIFIED. **OPEN in
  this RC until those receipts are published and checked here.**
- Caveats: compared with the fresh run from 800d78a9 on (`inputs_commit` masked); records from
  earlier drivers carry caveats that replay did not reproduce.
- Olean reproducibility is **not** claimed: 28 of 3966 oleans differed bitwise between acc4-flag
  and its fresh replay; replay matches the closure's modules by name.
- `published_statement` is `{}` in records from drivers before it was filled in; the strict
  component is computed from the Final theorem instead.
- acc4-flag's caveat names an older `tools/certify/solidity-lean.rev` pin (d0ab5d63) than its base.

## Receipts

Labels: **one-full-run** = the exit comes from its own complete driver run;
**comparison-reuse** = an edited copy of an existing record or run checked against it;
**exact-pin** / **compatibility-check** for replays, as defined under Pins.

### Positives

| Record | Driver | Verdict | Replay | Accepted at RC pin |
|---|---|---|---|---|
| acc4-flag (`Certified/record/acc4-flag/`, from records d66e60bf) | 6d0f2621 | CERTIFIED, tier certified, strict holds, exit 0 (one-full-run) | exact-pin fresh-clone replay at 6d0f2621, 18/18 pins SAME, exit 0 (`Certified/record/acc4-flag-replay/`, from 4df9c420) | **No**: 6d0f2621 is not an ancestor of 800d78a9 and differs from it in 17 driver files and 27 compiler files. Exact-pin at 6d0f2621 only. |
| H1 SimpleStorage (held-out runner T6) | 800d78a9, or 1844041e if started before the pin moved (then not an RC-pin record) | pending | pending | pending |
| H2 ViewAndPure (runner T7) | 800d78a9 | pending | pending | pending |
| H3 Mapping (runner T8) | 800d78a9 | pending | pending | pending |

acc4-flag, as checked by the reviewer: theorem `Certified.flag_4ce5cf9a.Final.final`, shape
`Generic.Expected`, `assumptions := []`; axioms `propext, Classical.choice, Quot.sound`; closure
3966, replayed 3966, trusted 0, unaccounted 0; bytecode sha256
f689833eb749e7509b4fb038bd8a4e251e77daa10aed088b2b12fa70ab76f69f, compiled in the run by solar
6d0f2621 (binary sha256 62c9d6ed…870f, built from that commit); source sha256 4ce5cf9a…388d. In
both its `replay/` and the replay's `fresh-run/`, `record.json`'s `final`, `replay`, `statuses`
and `caveats` equal the hashed `certify-record.json`'s, and both `MANIFEST.sha256` files check.

### Negative exits

| Case | Driver | Exit | Kind |
|---|---|---|---|
| acc4-flag in-run negatives: opcode edit, stale bytes, substituted artifact, wrong gas bound, wrong postcondition, no allowed status, vacuity variants, name hijack/alias/macro, skipped kernel, sorry proof | 6d0f2621 | every variant refused (`driver.log`: "final_neg: every variant refused") | one-full-run (inside the acc4-flag run) |
| replay with edited claims (final.theorem, final.statement, replay counts, a dropped module, emptied exclusions) | c09510a3 | **exit 0 CERTIFIED: failure**, fixed in 1844041e | comparison-reuse |
| archived input edited + run_files rehashed | 1844041e | **exit 0 CERTIFIED: failure**, fixed in 800d78a9 (receipt pending here) | comparison-reuse |
| input-rehashed, shape-rehashed, caveats-forged; unedited control | 800d78a9 | reported REJECTED ×3, control CERTIFIED; receipts pending here | comparison-reuse |
| replay of each held-out record with an edited claim | 800d78a9 | pending | comparison-reuse |
| `--tier lifecycle` on each held-out case | 800d78a9 | pending; expected usage error (tier not offered, exit 2), recorded as such, not as BLOCKED | one-full-run |

## Files

- `Certified/record/acc4-flag/`: byte-identical to records d66e60bf (and 4df9c420);
  `sha256sum -c MANIFEST.sha256` inside it.
- `Certified/record/acc4-flag-replay/`: byte-identical to 4df9c420; same check.
- `tests/heldout/rc-2026-11-15/`: byte-identical to e0564a28; `sha256sum -c SHA256SUMS`.
- `RC.MANIFEST.sha256`: sha256 of every file above, from the repository root
  (`sha256sum -c RC.MANIFEST.sha256`).
