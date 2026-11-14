# pair-spec lane: UniswapV2Pair published statement (swap, skim, sync)

Status: **statement fixed and composition wrapper kernel-checked against named stage Props;
non-vacuity, binding and negative controls proved; no stage theorem exists yet, so nothing
end-to-end is proved for the pair.** Kernel axioms of every theorem below: a subset of
propext, Classical.choice, Quot.sound (checked by #guard_msgs on #print axioms). No sorry,
native_decide, bv_decide or ofReduceBool.

## Files

- `sl-pair-spec.patch`: git am onto solidity-lean storm/base (d54dabf). Three commits (641f959 statement, 19376af reentrancy admission, 362b13a inputs module).
- `solar-pair-spec.patch`: git am onto solar storm/solar-sq (237518e9e). Two commits (62b2e8681 dynamic params in --emit-lean-spec, b6459dce9 final.py kind `open_functional`).
- `driver/shape.json`, `driver/Proofs.lean`: certify driver input for the pair (kind `open_functional`); `final.py` renders `Statement.lean` from it and `Proofs.lean` proves the driver's NonVacuous from `PairSpec.nonVacuous` (builds). `proof` names `published`, which does not exist until the stage theorems land, so check_final is not run.
- `evidence/PairRun.t.sol`: forge test on the compiled runtime (untrusted evidence, not part of any proof). Reads `pair.hex` / `pair-noupdate.hex` (not committed: compile output of the GPL sources).

## What is proved (solidity-lean, `lake build ContractsUniswapV2PairSpec`)

| Theorem | What it says | Status |
|---|---|---|
| `SolidCore.Refinement.Shapes.OpenFunctional.bytecode_any` (Verify/ShapeOpen.lean) | open-world shape: every result of the bytes in every admitted environment is allowed and meets the spec for some admitted world, or is inert | proved |
| `SolidCore.Spec.UniswapV2.PairSpec.published_of_stages` (PairSpec/Published.lean) | `Bound → (∃ c, contract? = .ok c) → (Equiv*) → (Term*) → (Meets*) → Statement` | proved (an implication: the stage theorems are its hypotheses) |
| `SolidCore.Spec.UniswapV2.PairSpec.bytecode_of_statement` | what `Statement` gives of the bytes | proved |
| `SolidCore.Spec.UniswapV2.PairSpec.nonVacuous` (PairSpec/NonVacuous.lean) | the exported spec rejects a valid call's result (sync from empty storage, supply 0 → 1) in every world | proved |
| `SolidCore.Spec.UniswapV2.PairSpec.Negative.bound` | export `SolarTV.Export.UniswapV2Pair.bytecode` = bytes of solar's plain compile (4446 bytes), kernel decide | proved |
| `…Negative.altered_not_bound` | altered jump (first PUSH2 t JUMPI, t = 0x0156 → 0x0157) fails the binding by mismatch | proved |
| `…Negative.swap_k_holds` / `wrongK_rejects` | the K clause with fee 4/1000 (SpecWrongK, generated mutant) rejects the swap 10000/10000 → 11000/9094 (1000 in, 906 out) that the published clause accepts | proved (formula level) |
| `…Negative.noUpdate_rejected` | the published K clause rejects a swap paying 906 out with reserves left at 10000/10000 | proved (formula level) |

## The published statement (`SolidCore.Spec.UniswapV2.PairSpec.Statement`, PairSpec/Statement.lean)

`Bound ∧ (KeccakModel → ∃ c, SolidCore.Verify.VC.UniswapV2Pair.contract? = .ok c ∧
OpenFunctional fuel c code EnvOk Admit Valid Allowed Post)`

- bytes: `code` = the `-Zemit-lean-stages` export, bound by exact equality to the plain compile's bytes (`-Ogas --evm-version osaka`).
- valid calls: `swap(a0, a1, dst, data)` with data ABI-encoded at offset 0x80 (any data < 2^32 bytes, so the callback path is in scope), `skim(dst)`, `sync()`; clean words, no value, any storage.
- admission: `Admit W := Wide W ∧ PairFramed W` `PairFramed` excludes worlds whose answers change the pair's own storage (SolidCore's `adoptWorld` would otherwise let a callee rewrite reserves); runs only explainable by such a reentrant world fall to `Unadmitted` and are reported, not hidden. The framework fixes the caller at 0x2000, so full reentrancy (a token calling back into the pair's ERC20 functions) is not modeled yet.
- environment (requirement E): bytecode runs among any well-formed list of other accounts with any code/storage (`Target.runWithIn`, own logs only); source runs in every admitted open world (`World.Open`, return data < 2^64, codes < 2^160). Termination and spec are ∀ admitted worlds; equivalence picks a world per run (∃) — causal consistency of that world with the environment's code is not stated.
- allowed statuses: every status (declared vacuity): swap/skim/sync bubble callee revert data verbatim, so no revert data can be excluded; the spec constrains successes only.
- spec: `Shapes.bundlePost` of solar-verify's export (`SolidCore.Spec.Export.UniswapV2Pair.UniswapV2Pair`) with identity ghost step; ERC20 invariants assumed before, required after.
- named premise: `KeccakModel` := `NestedSlotsSeparated [1, 4] [2]` (current premise name; switch to the keccak-model lane's `KeccakModel` when it lands). Premise, never an axiom.

Why open world: `Shapes.Functional`'s target (`Target.preState`) holds only the pair and its caller; every token call then reaches an account without code, every swap/skim/sync reverts, and a success spec holds vacuously. A closed-world Pair statement would be empty.

## Stage theorems the wrapper needs (stub Props in PairSpec/Stages.lean)

| Prop (namespace `SolidCore.Spec.UniswapV2.PairSpec.Stages`) | expected theorem name | owner |
|---|---|---|
| `EquivSwap c`, `EquivSkim c`, `EquivSync c` (`EquivOn c ValidX`: per-run equivalence in every admitted env) | `SolarTV.Export.UniswapV2Pair.Ctx.equiv_swap` / `_skim` / `_sync` | pair-stages-b |
| `TermSwap c`, `TermSkim c`, `TermSync c` (source halts in every admitted world) | `SolidCore.Spec.UniswapV2.Pair.terminates_swap` / `_skim` / `_sync` | pair-stages-b |
| `MeetsSwap c`, `MeetsSkim c`, `MeetsSync c` (`KeccakModel → ∀ W, Admit W → Meets (solidCoreIn W fuel) c ValidX (Post W)`) | `SolidCore.Spec.UniswapV2.Pair.swap_holds` / `skim_holds` / `sync_holds` | pair-spec (spec connection, not done) |
| source acceptance | `SolidCore.Verify.VC.UniswapV2Pair.contract_ok` (exists in storm/base, Pair/Contract.lean) | done |

Final theorem once they land: `published_of_stages Negative.bound contract_ok (fun c hc => ⟨…⟩) …`.

## Statuses (separately)

- equivalence: **missing** (stub `Equiv*`; needs pair-stages-a/b over `Target.runWithIn`, i.e. EthLib with other accounts — current stage machinery runs `Target.preState` only).
- termination: **missing** (stub `Term*`).
- spec: **missing end to end**; statement fixed and non-vacuous; spec connection (`Meets*`) not proved: `spec_connect.py`/`eraseFn` do not erase functions with external calls.
- resources: **not stated** (no gas bound; callees spend gas).
- remaining assumptions: `KeccakModel` (premise); source model trust (SolidCore checked contract = meaning of the source); constructor/deploy not covered (any storage).
- excluded: mint, burn (exported ensures use statement-level ghosts `mintAmount0 = amount0` etc. whose values depend on token answers; needs a world-dependent ghost step, `Post W` already takes `W` for it), ERC20 functions, permit, initialize, getters.

## solar change (`solar-pair-spec.patch`)

`--emit-lean-spec` refused any function with a `bytes`/`string` parameter (swap). Now such a parameter is exported as its ABI head word `(.uint 256)`; a spec that reads it is refused. Tests: `cargo test -p solar-verify --test cases emit_lean_spec` (snapshot updated, new refusal case).

## Commands

```
# solidity-lean at storm/base + sl-pair-spec.patch; solar at storm/solar-sq + solar-pair-spec.patch
cargo build --release -p solar-compiler --bin solar -p solar-verify --bin solar-verify   # in solar
scripts/verify/uniswap_v2_gen.sh
SOLAR_DIR=<solar> SOLAR=<solar>/target/release/solar SOLAR_VERIFY=<solar>/target/release/solar-verify \
  scripts/verify/uniswap_v2_pair_spec.sh      # Spec, SpecWrongK, Bytecode, Runtime (not committed)
LEAN_NUM_THREADS=1 lake build -KleanMemory=5000 ContractsUniswapV2PairSpec
```

## Missing / next

1. Spec connection `swap_holds`/`skim_holds`/`sync_holds` in the open world.
2. World-dependent ghost step for mint/burn, then add them to `Valid`.
3. check_final for kind `open_functional` (final.py renders it; check_final not extended).
4. Lean-level evidence that the mutants' observables arise from bytes (negatives are formula-level; forge evidence below).

## Evidence (forge, untrusted)

`evidence/PairRun.t.sol`, runtime etched at a fixed address with two minimal ERC20 tokens, all 4 tests pass:
- real bytes: swap(0, 906) from reserves 10000/10000 after 1000 token0 in succeeds, reserves 11000/9094; swap(0, 907) reverts (K).
- mutant without swap's _update (`pair-noupdate.hex`): swap(0, 906) succeeds with reserves left at 10000/10000, the observable `noUpdate_rejected` rejects.
- closed world (token addresses without code): swap, skim and sync all revert, which is why a closed-world statement is vacuous.

## Kernel VC discharge of solar-verify's model (separate from the statement)

`Contracts/UniswapV2/VC/discharge.sh <solar> <solar-verify> <out> Pair` with `DISCHARGE_BACKENDS='smt=vc_smt;vc_valid=vc_valid@90'`: in progress at this push (exported so far: initialize 5, _update 4, mint 14 obligations). These discharge solar-verify's VCs of its own model of the source, not the source-to-bytes or spec connection.

