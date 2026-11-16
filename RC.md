# Release candidate 2026-11-15 (solidity-lean)

Status: **not a passing release candidate. Held-out positives: 0 of 3** in the original draw (H1
REJECTED, H2 REJECTED on a resource limit, H3 BLOCKED), and **0 of 1** in the separate second draw
(H4 REJECTED; closed at H4). There is no exact-pin positive at the RC driver pin. This file is
complete as a report of those results; acc5 is not needed for it. The acceptance reviewer, the only publisher of RC artifacts,
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
| Held-out set | **original draw** H1-H3 (reviewer judgment, frozen before any run): `alpharush/rc-heldout` @ e0564a28100931a9986af9a848a57bc2bd835c67; the held-out denominator of this RC, fixed at 3. A separate second draw H4-H5 is reported apart (see Receipts). Both copied here under `tests/heldout/rc-2026-11-15/` |

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
| return values, view/pure functions | admitted by the envelope; **no certified instance**. H1's `get() returns (uint256)` with `result == num` is REJECTED at the spec step (see Receipts) | none (H2 REJECTED, resource) |
| checked arithmetic (Panic 0x11) | supported | none (H2 REJECTED, resource) |
| `mapping(K => V)` of value types: read and write in a declared function | supported with premise (Keccak-256 separation over each call's footprint); H3's probe agrees on `get` and `set`, but H3 as a whole is BLOCKED | none |
| public mapping (its compiler-generated getter), `delete` of a mapping element | BLOCKED: the generic source check has no erasure for either ("source tree undefined (erasure)"). `envelope()` and `docs/SUPPORTED_ENVELOPE.md` admit both, so this is caught only at the source check, which fails closed (exit 3). Any contract with a `public` mapping is outside the subset at the pin | - |
| state-variable initializers / constructor without parameters | runtime tier only: the storage is any storage that lists every slot the constructor writes (`Generic.Covers`: those slots, any values); the constructor's run is not part of the claim | none (H2 REJECTED, resource) |
| constructor with parameters | BLOCKED (envelope) | - |
| recursion (a function calling itself) | admitted by `envelope()`, refused later at the gas-need step ("no cut points … a recursive call"); outside the subset at the pin, reported as REJECTED, not BLOCKED (H4) | - |
| deployment / init code / lifecycle | BLOCKED (not offered): the pin has no lifecycle or constructor tier, and `--tier lifecycle` exits 2 "tier not offered". This is a scope limit, not a failure of the certified runtime claim | - |
| caller other than 0x2000 (any-caller) | proved for acc4-flag (driver 6d0f2621) no-value calls, any caller; not wired into the generic driver, so no RC-pin record has it; calls with value and contracts that read `msg.sender` are outside it (`BOUNDARY.md`) | acc4-flag only: solidity-lean `alpharush/t2-any-caller` @ a388f26133e3defa8f3ae18f675cf5b231981aee (not merged into this RC) |
| loops (for/while/do), certified bytes | BLOCKED: the generic driver at the pin does not take loops | - |
| loops, source-level obligations | gate only, SMT level: solar-verify's initiation, consecution, termination and exit obligations all unsat (z3), plus a required nonvacuity witness. Not kernel-certified; no MIR or bytecode binding; source-loop binding for `Counter.bump` only | `Counter.bump`, `Gcd.gcd` (gate ACCEPT, solidity-lean ca0d05b6) |
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
- **Resources:** H2's `SpecConnect.lean` check needs more than Lean's default 6000 MB on a 14 GB
  Hand (peak 14.25 GB process tree); the generic stage's memory use is a blocker for contracts
  of that size.
- **Storage getter returning a word: spec_connect gap.** H1's `get() returns (uint256)` with
  `@custom:ensures result == num` is refused at `spec_connect` (omega fails, `sorryAx` in
  `get_holds`), so no function that returns a storage word has a certified spec at the pin.
- Constructor / deployment / lifecycle: BLOCKED (no tier at the pin).
- Any-caller: proved for acc4-flag's archived bytes, no-value calls, every `Context.Ok` caller
  (`alpharush/t2-any-caller` @ a388f261: `Generic.Expected` kernel-checked, axioms `propext,
  Classical.choice, Quot.sound`, `lake -R build VerifyGenericAnyCaller` exit 0 as reported by T2).
  The reviewer checked that its diff from b0196e92 is `Verify/Generic/{CheckLFrom,AnyCaller}.lean`,
  `Instances/FlagAnyCaller.lean`, `BOUNDARY.md`, `lakefile.lean` (+13) and a mode-only change to
  `envelope_check.py` (100644 to 100755), and adds no `sorry`, `admit` or `axiom` in Lean source
  (the only matches in the commit are negative-test lines in carried-in record logs); the build was
  not rerun here. Not wired into the generic driver. **Cited by sha only, not merged**: a388f261's
  parent is bd7651009cae5f57c8706556a06ee156412812a8 (two commits on 44572c15), not 44572c15, and the
  commit carries the `envelope_check.py` mode flip.
- OPEN: E6 any-caller fresh-byte binding. a388f261 proves the archived Flag record for any caller
  with no-value calls, but `Transfer.expected` is still default-context, and
  `Certified.certified_any_caller` has arbitrary-caller resources but a fixed-caller
  `TargetPost`. Nothing binds a fresh run's bytes at 800d78a9 for any caller.
- OPEN: acc5 fresh replay.
- OPEN (one gap): Counter loop-head consumer. Reviewed: T4 `alpharush/t4-loopvc-rc` @
  d365320e3010ab60166e3ebc2dec618c2d89fe9c, clean replay receipt 19112ca845cd05981f66550d90d321aa3c35110f
  (`Verify/LoopSource/RC/replay-receipt/`: fresh worktree, `LEAN_NUM_THREADS=1`, exit 0, 32/32
  checks). Met: (a) pinned hashes: `MANIFEST.json` pins sources, spec lines, options, compiler,
  loop-head map and SMT/VC hashes, and the replay re-checks each and re-emits the map identically;
  (b) satisfiable witness: `pre_witness` (n = 3, count = 5, limit = 8), proved by `decide`;
  (c) wrong-map negatives: `wrong_slot` and `swapped_var` rejected by the kernel (exit 1), and
  stale compiler/source rejected (exit 3, 1); (d) manifest and clean replay; (e) axioms: every
  theorem in `RC/Receipt.lean`, headline included, guarded to `propext, Classical.choice,
  Quot.sound`, and `body_runs_vc` shown to reach `Counter.obs_valid`, `Counter.M` and
  `Counter.script`. **Gap: no check pins the headline's type.** `body_runs_vc : … → BodyRuns
  (env ev tbl) fuel fn bumpBr` matches the README's headline by the reviewer's reading (`bumpBr`'s
  normal leaf writes slot 0 := count + n), but nothing in the replay compares it with an expected
  statement written apart from the proof (as the generic driver does with `final : Statement`), and
  other theorems of the same type exist in the tree (`SourceBump.lean:118`, `LoopBinding.lean:151`).
  Closing it: an `example : <stated headline> := body_runs_vc` (or a separate statement module) in
  `Receipt.lean`, checked by the replay. Note: this route's compiler is solar fd53f637
  (`alpharush/t1-loop-heads`), not the RC driver 800d78a9, and it is a source-semantics claim only.
- OPEN: MIR / bytes / gas binding of any loop result.
- Loops: certified bytes BLOCKED at the pin. The loop gate (below) is an SMT-level source check
  only. Lean-checked: none accepted yet (T4, solidity-lean 3b4f52e5). The Counter source-consumer edge
  (d365320e, replay 19112ca8) is **pending its headline type check** (see the Counter item above);
  `Gcd.gcd`'s Lean binding is OPEN; MIR, bytes and gas are OPEN. `Gcd.gcd` also has no source-loop binding (its body
  branches). Gas and resource certification for loops is BLOCKED (no gas obligation or fuel-bound
  interface).
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

### Held-out verdicts and their receipts

| Draw | Case | Verdict | Receipt (record dir in this branch; source commit) |
|---|---|---|---|
| original (denominator 3) | H1 SimpleStorage | REJECTED, exit 1 | `Certified/record/heldout-h1-simplestorage-rejected/`; https://github.com/paradigmxyz/solidity-lean/tree/fe49ed41c1604e877df706525b640e17758c76cf/Certified/record/rc-heldout-h1-simplestorage |
| original | H2 ViewAndPure | REJECTED, exit 1 (resource) | `Certified/record/heldout-h2-viewandpure-rejected/`; https://github.com/paradigmxyz/solidity-lean/tree/85b1dad91a7d04b809d2d1ec3e4e48e95d524b52/heldout-records/rc-2026-11-15/H2-ViewAndPure |
| original | H3 Mapping | BLOCKED, exit 3 | `Certified/record/heldout-h3-mapping-blocked/`; https://github.com/paradigmxyz/solidity-lean/tree/4032285f1f264772d613982e63e06478b1d53af2/heldout-records/rc-2026-11-15/H3-Mapping-BLOCKED |
| second (denominator 1, closed) | H4 FunctionModifier | REJECTED, exit 1 | `Certified/record/heldout-h4-functionmodifier-rejected/`; https://github.com/paradigmxyz/solidity-lean/tree/20da86ba5336207f822b6c43181aca696f2c4f82/heldout-records/rc-2026-11-15/H4-FunctionModifier-REJECTED |
| second | H5 Account | not run | - |

Cases and specs: https://github.com/paradigmxyz/solidity-lean/tree/e0564a28100931a9986af9a848a57bc2bd835c67/tests/heldout/rc-2026-11-15
(original) and https://github.com/paradigmxyz/solidity-lean/tree/aa9191531b28e5cd44095f8bd680f789a61729c9/tests/heldout/rc-2026-11-15/draw2
(second). Every receipt above is one-full-run; `--tier lifecycle` exits 2 on every run case.

### Positives

| Record | Driver | Verdict | Replay | Accepted at RC pin |
|---|---|---|---|---|
| acc4-flag (`Certified/record/acc4-flag/`, from records d66e60bf) | 6d0f2621 | CERTIFIED, tier certified, strict holds, exit 0 (one-full-run) | exact-pin fresh-clone replay at 6d0f2621, 18/18 pins SAME, exit 0 (`Certified/record/acc4-flag-replay/`, from 4df9c420) | **No**: 6d0f2621 is not an ancestor of 800d78a9 and differs from it in 17 driver files and 27 compiler files. Exact-pin at 6d0f2621 only. |
| H1 SimpleStorage (held-out runner T6) | 800d78a9 (clean; its solar binary reports `binary_commit` c09510a3, which differs from 800d78a9 only in `tools/certify/generic.py` and `test_generic.py`, so the compiler source is the same. A 1844041e attempt was stopped in its probe build and wrote no record) | **REJECTED, exit 1** (one-full-run): "spec: get_meets0 does not check: omega could not prove the goal (SpecConnect.lean:163)"; `get_holds` and `get_holds_in` depend on `sorryAx`, so `spec_connect` refused the functions and `scripts/certify --require-final` exited 1. Only partial result: `set(uint256)`'s spec theorems checked. tier_reached none; bytecode sha256 6e95f821ecc2c71682bb59cd089429e0ab967f2cb33da8a32ffbce7135e9d402, gas bound 1944803; record.json sha256 4758becf…c96e. Record dir `Certified/record/heldout-h1-simplestorage-rejected/`, byte-identical to `alpharush/t6-heldout-records` @ fe49ed41 | not applicable (nothing certified) | **No: REJECTED.** The spec is unchanged and states only `result == num`; a re-elaboration outside the driver shows omega's possible counterexample over `pre.time`, which the spec never mentions. The runner reads it as a gap in the generic stage's proof of a returned value, not a spec defect. Case not edited or re-run. Held-out negative result; the failure fails closed |
| H2 ViewAndPure (runner T7) | 800d78a9 (clean), inputs commit 5eaae9e1 | **REJECTED, exit 1** (one-full-run, wall 45:53): Lean went over `LEAN_MEMORY=6000` while checking `SpecConnect.lean` and segfaulted (exit 139), so `spec_connect` refused the functions. Probe: `PROBE constructor: returns`, storage `[(0, 1)]`, all 3 functions agree. tier_reached none; bytecode sha256 9ee97f8f…a8c97; peak RSS 14.25 GB (process tree) on a 14 GB Hand. 23 earlier theorems on `propext, Classical.choice, Quot.sound` only (as reported). Driver log: "REJECTED: resources: 1 resource failure(s) in the build, not a proof failure (LEAN_MEMORY=6000)". Record dir `Certified/record/heldout-h2-viewandpure-rejected/`, byte-identical to `alpharush/heldout-h2-records` @ 85b1dad9 (that branch's parent is the `rc-heldout` tip aa919153, i.e. 44572c15 plus held-out test commits only; the record pins base 44572c15) | not applicable (nothing certified; no `statuses.equivalence` to edit) | **No: REJECTED (resource).** Not a failed proof and not a spec defect; case not edited or re-run. The coordinator authorised one higher-memory **diagnostic** rerun; it is reported separately, if made, and never replaces this verdict |
| H3 Mapping (runner T8) | 800d78a9 (binary dc65961e…b845) | **BLOCKED, exit 3** (one-full-run): "generic source check (2x, first myMap(address): source tree undefined (erasure))"; the second is `remove` (`delete myMap[_addr]`). tier_reached none; bytecode sha256 9071475602f625d442ffcbba8fcfac971109482af02166d1892f846615cefda6, gas bound 9237812; record.json sha256 7df52bde…0f99 (record dir `Certified/record/heldout-h3-mapping-blocked/`, byte-identical to `alpharush/heldout-h3-blocked` @ 4032285f; its record.json has no solidity_lean field because the run stopped before the base was used, so the base rests on the driver default: no `--base` was given, and `tools/certify/solidity-lean.rev` at 800d78a9 is 44572c15) | not applicable: `--replay` of the BLOCKED record exits 1 "the record is BLOCKED: nothing to replay" | **No: BLOCKED.** Not a spec defect; case not edited or re-run. Counts as a held-out negative result |

**Original held-out draw (H1-H3, e0564a28), denominator fixed at 3: 0 certified.** H1 REJECTED
(exit 1), H2 REJECTED (exit 1, resource), H3 BLOCKED (exit 3). Both failures are genuine failures of the original draw and stay
counted in it; nothing replaces or dilutes them.

### Separate second draw (own denominator; not part of the original draw)

The original selection protocol (`SELECTION.md` at e0564a28) defines no second draw. The H4-H5 draw
was made at the coordinator's request after H1 was REJECTED and H3 BLOCKED, by a rule written then
(`draw2/PROCEDURE.md`, frozen at 7f7230f7f0d67ac650d5771e4d7248839409ff2f before the draw; draw and
specs at aa9191531b28e5cd44095f8bd680f789a61729c9). Its results are reported here with their own
denominator and never count toward, replace or dilute the original draw's. **The coordinator closed
this draw at H4: result 0 of 1. H5 was not run.**

| Case | Driver | Verdict | Replay | Accepted at RC pin |
|---|---|---|---|---|
| H4 FunctionModifier (runner T8) | 800d78a9 (clean; `binary_commit` 800d78a9, binary dc65961e…b845) | **REJECTED, exit 1** (one-full-run, wall 4.1 s): "certify.py cannot write the stage proofs: error: no cut points for stage0 to mir1: place-reads: a recursive call into @decrement.body". Both envelope checks passed first (source inside; bytecode has no call, creation, gas or return-data opcode); it failed in the gas-need step, before the probe. tier_reached none; bytecode sha256 fe2739e8895b66eef5e4b71d9b5637901751962b4ed19ce7701ac9a96f19e0c3; no gas bound, probe or Final theorem. Record dir `Certified/record/heldout-h4-functionmodifier-rejected/`, byte-identical to `alpharush/heldout-h4-rejected` @ 20da86ba | not applicable: `--replay` exits 1 "the record lists no run files" | **No: REJECTED.** Case not edited or re-run. The recursion is not an envelope reason, so the driver reports REJECTED rather than BLOCKED; it still fails closed |
| H5 Account | - | **not run**: the draw was closed at H4 (coordinator, 20:28 CST) | - | - |

acc4-flag, as checked by the reviewer: theorem `Certified.flag_4ce5cf9a.Final.final`, shape
`Generic.Expected`, `assumptions := []`; axioms `propext, Classical.choice, Quot.sound`; closure
3966, replayed 3966, trusted 0, unaccounted 0; bytecode sha256
f689833eb749e7509b4fb038bd8a4e251e77daa10aed088b2b12fa70ab76f69f, compiled in the run by solar
6d0f2621 (binary sha256 62c9d6ed…870f, built from that commit); source sha256 4ce5cf9a…388d. In
both its `replay/` and the replay's `fresh-run/`, `record.json`'s `final`, `replay`, `statuses`
and `caveats` equal the hashed `certify-record.json`'s, and both `MANIFEST.sha256` files check.

### Loop gate (source-level, SMT; not a certify record)

solidity-lean `alpharush/t4-loopvc-rc` @ ca0d05b6daa048b3765c3088c150b1f47e95a19c (two commits
on 44572c15), `Verify/LoopSource/RC/`; `RECEIPTS.json` sha256 1599b68940f527cdf1beedb633fc08742d13b26169ab68849bd33ab5a5e91505. Gate
`Verify/LoopSource/loopgate.py`: solar-verify (built from solar c09510a3, whose `crates/verify` is
unchanged at 800d78a9; binary sha256 102e482a…) with z3 5.4.1 (sha256 ae76a37c…). Exit 0 ACCEPT,
1 an obligation failed, 2 solar-verify error, 3 a loop kind missing, 4 VACUOUS. TCB for these
rows adds solar-verify's obligation generation and z3; no Lean kernel check is claimed here.
`Gcd.gcd` was chosen as held-out by the loop lane, not by the acceptance reviewer. Each row is
one-full-run (its own gate run); the reviewer read every `gate/<case>/gate.json` cited.

| Case | Gate exit | Note |
|---|---|---|
| Counter (`Counter.bump`, `for` over storage) | 0 ACCEPT | nonvacuity witness n=3, count=5, limit=8 |
| Gcd (`Gcd.gcd`, `while` with a branching body) | 0 ACCEPT | nonvacuity witness a=12, b=18 |
| CounterBadInit, CounterBadPres, CounterBadDecr, CounterBadExit | 1 each | each fails exactly its obligation kind |
| GcdBadInit, GcdBadPres, GcdBadDecr, GcdBadExit | 1 each | each fails exactly its obligation kind |
| GcdVacuous (contradictory `a > 0 && a < 1`) | 4 VACUOUS | solar-verify alone exits 0 with a warning; the gate rejects it, with and without `--assume` |

### Benchmark (informational, not a certification receipt)

solidity-lean `alpharush/eval-symm` @ 1928268bd23bf0f6d34bc939b04d3cd5b4413cae (`docs/eval/acc4.md`;
the branch is not based on 44572c15, but the measurement ran in a 44572c15 worktree):
acc4-flag's 26 generated modules re-elaborated, and 3,167 declarations (1,378 theorems)
re-added to the kernel alone: 0 rejected. Single thread, 26 modules in 105.9 s wall, peak RSS
2.93 GB. One run per cell.

### Negative exits

| Case | Driver | Exit | Kind |
|---|---|---|---|
| acc4-flag in-run negatives: opcode edit, stale bytes, substituted artifact, wrong gas bound, wrong postcondition, no allowed status, vacuity variants, name hijack/alias/macro, skipped kernel, sorry proof | 6d0f2621 | every variant refused (`driver.log`: "final_neg: every variant refused") | one-full-run (inside the acc4-flag run) |
| replay with edited claims (final.theorem, final.statement, replay counts, a dropped module, emptied exclusions) | c09510a3 | **exit 0 CERTIFIED: failure**, fixed in 1844041e | comparison-reuse |
| archived input edited + run_files rehashed | 1844041e | **exit 0 CERTIFIED: failure**, fixed in 800d78a9 (receipt pending here) | comparison-reuse |
| input-rehashed, shape-rehashed, caveats-forged; unedited control | 800d78a9 | reported REJECTED ×3, control CERTIFIED; receipts pending here | comparison-reuse |
| replay of each held-out record with an edited claim | 800d78a9 | pending | comparison-reuse |
| `--tier lifecycle` | 800d78a9 | exit 2 "tier not offered": H1 (`lifecycle-tier.log` in its record dir), H2 (one-full-run) and H3 (argparse invalid choice, no record; comparison-reuse). Lifecycle is BLOCKED (not offered), not a failure of the runtime claim | one-full-run per case |

## Files

- `Certified/record/acc4-flag/`: byte-identical to records d66e60bf (and 4df9c420);
  `sha256sum -c MANIFEST.sha256` inside it.
- `Certified/record/acc4-flag-replay/`: byte-identical to 4df9c420; same check.
- `Certified/record/heldout-h1-simplestorage-rejected/`: H1's REJECTED record, byte-identical to
  `Certified/record/rc-heldout-h1-simplestorage/` at fe49ed41; `sha256sum -c MANIFEST.sha256` inside it.
- `Certified/record/heldout-h4-functionmodifier-rejected/`: H4's REJECTED record (second draw),
  byte-identical to `heldout-records/rc-2026-11-15/H4-FunctionModifier-REJECTED/` at 20da86ba;
  `sha256sum -c MANIFEST.sha256` inside it.
- `Certified/record/heldout-h2-viewandpure-rejected/`: H2's REJECTED (resource) record, byte-identical to
  `heldout-records/rc-2026-11-15/H2-ViewAndPure/` at 85b1dad9; `sha256sum -c MANIFEST.sha256` inside it.
- `Certified/record/heldout-h3-mapping-blocked/`: H3's BLOCKED record, byte-identical to
  `heldout-records/rc-2026-11-15/H3-Mapping-BLOCKED/` at 4032285f; `sha256sum -c MANIFEST.sha256`
  inside it (its README.md is covered only by RC.MANIFEST.sha256).
- `tests/heldout/rc-2026-11-15/`: byte-identical to aa919153 (the first set as at e0564a28, plus `draw2/`);
  `sha256sum -c SHA256SUMS` there and in `draw2/`. `draw2/PROCEDURE.md` is the second draw's frozen
  rule; its seed is H1's `record.json` sha256, and every drawn case is reported whatever its verdict.
- `RC.MANIFEST.sha256`: sha256 of every file above, from the repository root
  (`sha256sum -c RC.MANIFEST.sha256`).
