# memory-patterns: end-to-end spec theorem (event_words)

Base: solidity-lean `f8a4a744` (#166 head), solar `902cccc2` (#2637).

- `memory-patterns-spec.bundle`: `git fetch memory-patterns-spec.bundle mem/spec`, 2 commits on `f8a4a744`.
  - `fix(spec): tree tactics decode address parameters`: `Verify/Spec/Tree.lean` (`tree_meets`, `tree_meets_fixed` split the address range test in `decodeWords`) and `Verify/Spec/TreeSucceeds.lean` (`tree_succeeds` steps may make no progress).
  - `feat(certified): event_words, end to end with its exported spec`.
- `solar-memory-patterns-spec.bundle`: 1 commit on `902cccc2`: `tools/certify/guard_build.py packages` no longer treats the package's own not-yet-written modules (the fresh spec export that a previous run's Shape.lean imports) as lake-package modules.

## The theorem

`Certified.event_words.Final.final : Certified.event_words.Final.Statement`, kind **certified**:

```
code bytes = runtimeBytes ∧ NonVacuous ∧
∃ c, EventWords.contract? = .ok c ∧
  Shapes.Certified (solidCore EventWords.fuel) c code (genericValid EventWords.fns [])
    (bundleAllowed Certified.event_words.gen.EventWords.Spec.EventWords ctxOfCall)
    (bundlePost   Certified.event_words.gen.EventWords.Spec.EventWords ctxOfCall idStep)
    (fun _ => 10210224)
```

The spec is solar-verify's export of `event_words.sol` from this run: `swap(a0,a1,b0,b1,to)` has `@custom:succeeds-if msg.value == 0`. `event_words.SpecConnect.swap_holds` connects it to SolidCore's checked contract, from the generic erased tree (which branches on `to` being a clean address). The heap-written Swap log is covered by equivalence, not by the spec, because the spec language can't name logs.

check_final: `axioms [propext, Classical.choice, Quot.sound]` (see [log](logs/certify-event_words.log)).

abi_hash was not used: solar-verify rejects `ensures result == uint256(keccak256(abi.encode(a, b)))` because the spec language has no keccak, so the only spec it could carry is `succeeds-if`.

## Receipts

- Driver: `SOLIDITY_LEAN_DIR=<solidity-lean> CERTIFY_ALLOW_UNPINNED=1 LEAN_MEMORY=9000 scripts/certify event_words.sol`. Memory: 9000 MB per Lean process. At 5000 and 7000, `SolidCore/Solidity/Interface/Statements.lean` hit the kernel's "excessive memory consumption" cap when built from cold.
- Regression for the tactic change: `lake -R -KleanMemory=6000 build events.SpecConnect Contracts.Counter.SpecTree Verify.Spec.TreeSucceeds Verify.ShapeSpecExport Contracts.Token.Lowering` gave EXIT 0, 2803 jobs ([log](logs/build-spec-tactics.log)).

## Driver outcome (EXIT 0)

```
check_final: Certified.event_words.Final.final : Certified.event_words.Final.Statement; axioms [propext, Classical.choice, Quot.sound]
replay: all 3942 modules of the published closure replayed by leanchecker in this run; 0 unaccounted
statuses: equivalence proved, termination proved, spec proved (Shapes.Meets of bundlePost of this run's export, NonVacuous), resources proved
negative statements (stale byte, substituted artifact, wrong gas, wrong post, no allowed status, vacuous spec, hijacked names): all refused by the kernel
CHECKED event_words (EventWords), published Certified.event_words.Final.final; not certified: not proved: none
```

Full log: [logs/certify-event_words.log](logs/certify-event_words.log). Record: [logs/record-event_words.json](logs/record-event_words.json).

The run says CHECKED rather than CERTIFIED only because of provenance. It started with these edits uncommitted (they are now the bundle's commits), from a trusted build directory without `CERTIFY_CLEAN_BUILD=1`, and with solc at an untracked `.cache/solc-0.8.35`. A rerun from the committed trees with `CERTIFY_CLEAN_BUILD=1` and `SOLC` outside the checkout should report CERTIFIED. I have not run that; it means a cold rebuild plus a replay of about 2 h.

The record's separate `end_to_end` field stays "not proved" because it counts only a `headline` file, whose modules the driver builds in step 6, before step 6b writes Final.lean. The spec-to-bytecode theorem is the published `Final.final` above.
