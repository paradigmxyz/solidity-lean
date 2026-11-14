# slice-source-mir: E3 for UniswapV2ERC20.transfer (source -> first lowered MIR)

Base: solidity-lean `alpharush/certified-translation` at 9fb89ee. Solar: `alpharush/certified` at
38b5232add998cd34a311c8cecf5737d38f9cce6 (stages exported fresh at build time, never a reference artifact).
Deliverable: `0001-feat-uniswap-v2-ERC20-transfer-source-stage-on-fresh.patch` (one commit, 10 files,
+338) and `slice-source-mir.bundle` (`git bundle` of 9fb89ee..work, the same commit).

## Result

E3 is PROVED for `transfer(address,uint256)`, with the private `_transfer` and SafeMath's checked
`sub`/`add` inlined, the two sequential `balanceOf` writes and the `Transfer` event, by the generic
source checker alone (`Generic.check`, `Generic.stageAtEnv`). No per-contract glue, no hand-written model.

**No checker gap was found.** The unchanged generic checker on the PR head accepts the fresh stage0:
SafeMath's `unchecked { require((z = x - y) <= x, ...) }` pattern (`eraseUnchecked`), solar's `lt`-based
overflow branches, mapping reads and writes through two-word Keccak-256 and the 3-topic log were already
in the fragment. So the generic checker needed no fix, and none was made.

## Theorems (namespace `SolidCore.Spec.UniswapV2.ERC20`)

| Name | Module | What |
|---|---|---|
| `SourceMir.check_eq` | SourceMirCheck | `kernel_rfl`: `Generic.check fuel 200 c.core stage0 [fn_transfer] .all = true`, evaluated by the kernel from the source text up |
| `SourceMir.check_ok` | SourceMirCheck | the same for any `c` with `contract? = .ok c` |
| `SourceMirDeploy.deploy_eq` | SourceMirDeploy | `kernel_rfl`: the constructor leaves exactly `deployed = [(3, kDomain)]` (DOMAIN_SEPARATOR) and no logs |
| `SourceMir.transfer_stage` | SourceMir | the E3 stage, below |
| `SourceMir.sourceEnvOk_inhabited` | SourceMir | `∃ o, SourceEnvOk o` (EthLib's oracle, `ethOracle`): the premise is satisfiable |
| `SourceMir.valid_inhabited` | SourceMir | `∃ call, genericValid0 fns deployed call` |
| `SourceMir.transfer_source_mir` | SourceMir | the closed edge: all of the above in one statement |
| `SourceMirNeg.refuses_<M>` (8) | SourceMirNeg | `kernel_rfl`: the same check of mutant `M` is `false` |

```lean
theorem transfer_stage (o : SolarTV.Machine.Oracle) (henv : Generic.SourceEnvOk o)
    {c : TypeCheck.CheckedContract} (hc : SolidCore.Verify.VC.UniswapV2ERC20.contract? = .ok c) :
    SolarTV.Stage (solidCore SolidCore.Verify.VC.UniswapV2ERC20.fuel) (SolarTV.MIR.Lowered.moduleSem o) c
      SolarTV.Export.UniswapV2ERC20.stage0 (Shapes.genericValid0 fns deployed)

theorem transfer_source_mir :
    (∃ c, contract? = .ok c ∧ ∀ o, SourceEnvOk o →
        SolarTV.Stage (solidCore fuel) (moduleSem o) c stage0 (genericValid0 fns deployed)) ∧
    (∃ o, SourceEnvOk o) ∧ (∃ call, genericValid0 fns deployed call)
```

`Stage` means every valid call's SolidCore observable (status, return data, revert data, storage, logs) is
the MIR's. `fns = [⟨0xa9059cbb, [uint256, uint256]⟩]`.

## Exact premises

* `SourceEnvOk o` (only premise): `CallerOk o` (the oracle's caller is `callerWord` = 0x2000, the caller of
  every `solidCore` run) and `HashOk o` (the oracle's Keccak-256 of 64 bytes of two words equals SolidCore's
  `solHash` of them, i.e. Keccak-256 itself). This is **not** a hash-separation premise. Both sides compute the
  same slots, so no injectivity is assumed and E3 needs nothing from hash-scope (`ScopedSep`). That premise
  belongs to E7. Satisfiable: `sourceEnvOk_inhabited`.
* Valid calls (`genericValid0 fns deployed`): transfer on any two argument words < 2^256 (a `to` word >= 2^160
  reverts on both sides), callvalue 0, any storage given as an entry list that lists slot 3 (`Covers deployed`).
* Trusted, stated: the frontend (E1) that generated `Contracts/UniswapV2/ERC20/Source.lean` from the port.

## Gaps against docs/CERTIFICATION_TARGET.md (named, not hidden)

1. **ANY caller is not stated, and no edge can state it today.** `SolarTV.Call` has no caller field, and
   SolidCore's `Statement.run` and EthLib's `Target.message` both fix `callerAddress = 0x2000`. The MIR side
   already holds for every oracle caller, but the source semantics and the byte-level run are fixed-caller.
   So the target's "Valid: ANY caller" needs a caller-parametric `Call`/`solidCore`/`ethLib` across E3..E5.
   That is a chain-wide change, outside this lane. E3 as delivered is for caller 0x2000.
2. Storage scope: valid storages must list slot 3 (any value). That is the generic stage's `Covers` of the
   deployed storage, not "any storage" literally.
3. Not in CI yet. Suggested step after "Generate and check the Uniswap V2 port", with the pinned solar binary:
   `SOLAR=<solar> scripts/verify/uniswap_v2_erc20_stages.sh && lake build -KleanMemory=6000 uv2_erc20 ContractsUniswapV2ERC20SourceMir`.
4. Memory margin: `SourceMirDeploy` peaks at 5.9 GB under `-M 6000` (the constructor's kernel evaluation).

## Negative controls (refused by execution)

`scripts/verify/uniswap_v2_erc20_mutants.py` edits one instruction of the fresh stage0 per mutant (it fails if
an edit does not apply), and the kernel evaluates the same `Generic.check` against the same checked source to
`false` for every one. The mutants are: NoDebit (debit sstore dropped), WrongSlot (balanceOf slot 1->2),
NoOverflowCheck (add overflow `lt`->`gt`), NoUnderflowCheck (sub `lt`->`gt`), WrongTopic (Transfer topic
last nibble), WrongReturn (returns 0), WrongRevertData (`ds-math-add-overflow` byte), SwappedLogArgs
(from/to topics swapped).

## Build receipts (hosted Hand, 14 GB, Lean v4.35.0, LEAN_NUM_THREADS=1, lake -KleanMemory=6000)

Peak = the largest single `lean` process RSS, sampled every second.

| Command | Exit | Peak |
|---|---|---|
| `scripts/verify/uniswap_v2_gen.sh` | 0 | n/a |
| `SOLAR=<solar 38b5232a> scripts/verify/uniswap_v2_erc20_stages.sh` (bytecode unchanged by -Zemit-lean-stages: cmp) | 0 | n/a |
| `lake build Contracts.UniswapV2.ERC20.SourceMirDefs` | 0 | 2182 MB |
| `lake build Contracts.UniswapV2.ERC20.SourceMirCheck` | 0 | 5364 MB |
| `lake build Contracts.UniswapV2.ERC20.SourceMirDeploy` | 0 | 5891 MB |
| `lake build Contracts.UniswapV2.ERC20.SourceMir` | 0 | 2613 MB |
| `lake build Contracts.UniswapV2.ERC20.SourceMirNeg` | 0 | 5296 MB |
| `lake build uv2_erc20 ContractsUniswapV2ERC20SourceMir` (after regenerating stages; 2785 jobs) | 0 | 676 MB (up to date) |
| `lake env lean -M 6000 Audit.lean` (`#print axioms` of all 15 theorems above) | 0 | 1355 MB |

Axioms: every theorem above, `check_eq`, `deploy_eq` and all 8 `refuses_*` included, depends on exactly
`[propext, Classical.choice, Quot.sound]`. `SourceMir.lean` pins `transfer_stage` and `transfer_source_mir`
with `#guard_msgs`. The scan of the new modules and the exported Stage0 for sorry / native_decide / bv_decide /
ofReduceBool / axiom / extern / implemented_by found none.

Input hashes (sha256): stage0 `Stage0.lean` dbbdffe888c2891471285365b6312cdb334aeb58b7d0989cca4e3a9cd8b87a59,
port `UniswapV2ERC20.sol` 762294af01e1257b4332c1808776df55ee39c2a837febd2cd4100568a7e15d4c, generated
`Source.lean` c581f1151d3e0f90c414c0682e491610ebfe42ecef47747d2bbe0fe5d501feaa. The generated sources and stages
are GPL-derived and are not committed. They are regenerated at build time.

## Files (all new or additive)

lakefile.lean (`uv2_erc20`, `ContractsUniswapV2ERC20SourceMir`), Certified/uv2_erc20/{options,.gitignore},
Contracts/UniswapV2/ERC20/SourceMir{Defs,Check,Deploy,,Neg}.lean, scripts/verify/uniswap_v2_erc20_{stages.sh,mutants.py}.
The `kernel_rfl` helper clones are per namespace, so `SourceMirDeploy` has its own namespace (Check and Deploy
in one namespace collide on import).
