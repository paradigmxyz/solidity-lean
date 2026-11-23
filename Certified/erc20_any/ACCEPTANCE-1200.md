# Acceptance package: the 1200-byte any-caller binding of UniswapV2ERC20.transfer

Prepared for a heavy run that has not happened yet. Nothing here is a result of that run. The
erasure-only evidence (the generic `.load` erasure, receipts at 02ece2b2) is not part of this
binding and does not count toward it.

## Pins

| what | pin |
| --- | --- |
| solidity-lean (LEAN_COMMIT) | 1f0db760f3ef35c7ffc974a24bae68d566788109 (`erc20-gates` tip) |
| Statement.lean at that commit | sha256 a8473b23e732a068690a87ce3eab03ce9072bec8b6a0b96e269267bdc99c7a9c |
| TransferExpected.lean (overlaid by run.sh) | 4332b47d3495790581a8d0d4f18f690bd8f3d5a6, sha256 8573c6944c24c3d578aaf1f52f127de5053c8e461318dfb3ba71c8fc767c988c |
| candidate compiler (CANDIDATE_COMMIT) | solar f71b7554d6e044cf974ac4f0e5f0b184cd96ff9b |
| candidate binary (CANDIDATE_SHA256) | 15808eeef2f5d5d021372d43a36ef491492cc8b2fc84b2c3b97a666a736381db |
| slice spec (SLICE_COMMIT) | solar 902cccc2cb1213219789780a39caf3c1d4d9f35e |
| harness | solar `erc20-gates` 2b2c3ddf3b20de8331676a998a6ba384bf5ece43, tools/certify/erc20_any |
| lean toolchain | leanprover/lean4:v4.35.0; packages from lake-manifest.json via `lake exe cache get` |
| emit options | Certified/uv2_erc20/options (`-Ogas --evm-version osaka`) |

Harness script sha256s at 2b2c3ddf: slot.sh 0f398932…1356, run.sh dfd2e4e3…552f, prep.sh
52ad71e5…0e99, replay.sh ca4329c0…b447, neg.sh 9079fcab…0d78, gen.py 3d8609f8…e884,
build_cap.sh 249a7bf6…2477, merge.py 76ad980f…6a88 (full values in receipts/harness.sha256).

## The theorem

`Certified.erc20_any.Final.final : Statement` (Final.lean), from
`Certified.erc20_any.Proof.statement`. `Statement` is the conjunction of: the imported source
unit and the manifest's pinned sources, compiler, options, EVM version and stages;
`SolarTV.Export.UniswapV2ERC20.bytecode = runtimeBytes` (the 1200 runtime bytes, gen.py checks
them against the fresh emit); the finite hash footprint; satisfiability for every real caller; and

    Expected src specAny runtimeBytes ∧ Expected src specScoped runtimeBytes

proved by `Proof.any` and `Proof.scopedExpected`.

* `specAny`: every context with `ctx.Ok` (caller < 2^160, not the contract), valid calls
  `Valid deployed` (any storage covering the constructor's, a clean address, any word, no value),
  post `PostAt ctx.caller = SeqPostAt a ∧ (ScopeAt a → TargetPostAt a)`, gas 8199112, no
  assumptions.
* `specScoped`: contexts `ctx.Ok ∧ ScopedSep (transferFootprint 1 a a)`, valid calls carry
  `ScopeAt a`, post `TargetPostAt a`.

The route is any-caller: the caller is the context's `a`, quantified over every real address,
not the fixed 0x2000 of the generic driver run.

## The gates and what proves each

| gate | definition | proved by (heavy) | checked here (light) |
| --- | --- | --- | --- |
| sequential self-transfer | `SeqPostAt a` with `seqStoreAt a s dst v` = debit then credit reading the debited state; `TargetPostAt`'s `a = dst` arm | `Proof.any` | `Gates.seqStoreAt_self`, `Gates.seq_self` |
| overflow | `SeqPostAt`'s success iff `v ≤ s[a] ∧ debitAt … + v < 2^256`; revert data `ds-math-add-overflow` / `ds-math-sub-underflow` | `Proof.any` | `Gates.seq_self_no_overflow`, `Gates.overflow_reachable`, `Gates.underflow_reachable` |
| finite hash footprint, satisfiable | `ScopeAt a` = `ScopedSep (transferFootprint 1 a dst)`, two preimages | `Proof.scopedExpected`, Statement's footprint conjunct | `Gates.footprint_eq`, `Gates.footprint_AB`, `Gates.footprint_AA`, `Gates.footprint_model`, `Gates.scoped_inhabited` |
| satisfiable premises | Statement's `∀ a, a < 2^160 → a ≠ selfAddress → ∃ call, specAny.Valid ⟨a⟩ call` | `Proof.satisfiable` | `Gates.satisfiable` |
| 1200 bytes | `bytecode = runtimeBytes` | `Proof.export_eq`, gen.py fresh-emit check | not checkable without the export |

The light statements, in Certified/erc20_any/Gates.lean:

* `seqStoreAt_self (a v) (σ) (hv : v ≤ slotValue σ (balKey a)) : seqStoreAt a (slotValue σ) a v = slotValue σ`
* `seq_self (h : SeqPostAt a call obs) (σ v) (hc : call = transferCall σ a v) (ha : a < 2^160) (hv : v < 2^256) : (obs.success = true ↔ v ≤ slotValue σ (balKey a)) ∧ (obs.success = true → obs.storage = slotValue σ)`
* `seq_self_no_overflow (a v σ) : (v ≤ slotValue σ (balKey a) ∧ debitAt a (slotValue σ) v (balKey a) + v < 2^256) ↔ v ≤ slotValue σ (balKey a)`
* `overflow_reachable : ∃ σ, 1 ≤ slotValue σ (balKey addrA) ∧ ¬ debitAt addrA (slotValue σ) 1 (balKey addrB) + 1 < 2^256`
* `underflow_reachable : ∃ σ, ¬ 1 ≤ slotValue σ (balKey addrA)`
* `footprint_eq (a dst) : transferFootprint balanceSlot a dst = [mappingPreimage a balanceSlot, mappingPreimage dst balanceSlot]`
* `footprint_AB : ScopedSep (transferFootprint balanceSlot addrA addrB)`, `footprint_AA` likewise for `addrA addrA` (kernel Keccak-256)
* `footprint_model (a dst) : ∃ h, SeparatedBy h (transferFootprint balanceSlot a dst)`
* `satisfiable : ∀ a, a < 2^160 → a ≠ selfAddress → ∃ call, specAny.Valid ⟨a⟩ call`
* `scoped_inhabited : specScoped.Contexts ⟨addrA⟩ ∧ specScoped.Valid ⟨addrA⟩ (transferCall deployed addrB 0)`

Gates.lean holds Statement.lean lines 143 to 215 (`deployed` through `specScoped`) byte for
byte; both ranges hash to d808925226244cebe3bca73e9642cd87e5c00ca15fd0693985992c775ac4e1d9. It
is not in a lake library and is checked with `lake env lean`.

What the light check does not show: `Expected` itself, the 1200 bytes, any-caller fresh bytes, or
that `ScopedSep` holds for every address pair. `footprint_AB`/`footprint_AA` are two concrete
pairs and `footprint_model` is a model hash, not Keccak-256. A bounded model over a few addresses
or an n=8, K≤Kmax family is not a substitute for the general result. Keccak separation for all
pairs stays the scoped premise `ScopeAt`, printed in the statement.

## Box argv (waits for its place in the box queue, after T4 v7)

Two sequential slots on m4-metal-large (the replay is about 168 min at PAR 4, longer than one 2 h
box), never two boxes at once. Under ~/w: solar at 2b2c3ddf, solidity-lean, the candidate binary
at ~/w/candidate-bin/solar, and ~/w/env.sh exporting

    LEAN_COMMIT=1f0db760f3ef35c7ffc974a24bae68d566788109
    CANDIDATE_COMMIT=f71b7554d6e044cf974ac4f0e5f0b184cd96ff9b
    CANDIDATE_SHA256=15808eeef2f5d5d021372d43a36ef491492cc8b2fc84b2c3b97a666a736381db
    SLICE_COMMIT=902cccc2cb1213219789780a39caf3c1d4d9f35e

with every CERTIFY_ALLOW_* unset. Then:

    slot 1: bash ~/w/solar/tools/certify/erc20_any/slot.sh 1 <box expiry, Unix time>
    slot 2: bash ~/w/solar/tools/certify/erc20_any/slot.sh 2 <box expiry, Unix time> <slot 1's out/replay, copied in>
    after the build, on a slot box: bash ~/w/solar/tools/certify/erc20_any/neg.sh ~/w/solidity-lean <slot out>
    on the hosted Hand: python3 tools/certify/erc20_any/merge.py <receipt> slot1/out/replay slot2/out/replay

Defaults kept: BUILD_JOBS 12, budget 75% of memory, PAR 4, REPLAY_MARGIN 50, kill 12 min before
expiry, run.sh's `lake build -v -KleanMemory=12000` under build_cap.sh's cgroup cap.

## Expected receipts

Per slot, ~/w/slot<N>/: steps (one line per step: port, candidate, verify, core, slice, prep, run,
replay, each with exit, wall and peak RSS), gate.txt (build_cap admission and PASS/FAILED per step,
replay gate; any FAILED voids the slot), mem.tsv, <step>.log and <step>.time, <step>.peaks,
candidate-version, tree-status, tree.diff, replay.log, replay.time;
prep/: producer, inputs.sha256, prep-steps; out/: fresh.json, identities, artifacts.sha256, steps,
check_final.log, replay/ (plan, batches, batch-exits, gate.txt, samples.tsv, b<INDEX>.out).
Negatives, neg/results: control pass; byte_first, byte_last, source_pins, source_contract,
prop_credit_plus_one, prop_self_no_overflow, prop_unchecked_overflow, ctx_self_caller,
gas_minus_one, footprint_dropped and the fresh-byte case (gen.py on a mutated emit) each fail.
Merge: one receipt naming every planned module with its slot and batch, or a refusal.

Acceptance needs all of: check_final exit 0 on `erc20_any.Final`, with `#print axioms final`
only propext, Classical.choice, Quot.sound; gen.py's fresh emit equal to `runtimeBytes` (1200
bytes) from the pinned binary; every planned module replayed exactly once (merge receipt), no
module trusted by directory; both slots' plans byte-identical; no FAILED gate line; every negative
as listed.

## Gates that stay open

MapSlotsSeparated (hsep) is not discharged. Instantiated finite-footprint satisfiability for
Keccak-256 at every pair is not discharged; the binding carries it as `ScopeAt`. Runtime tier
only: no deployment, constructor, lifecycle or reentrancy. The gas figure bounds when the bytes
match the source and is not a no-OOG guarantee.
